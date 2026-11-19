import test from 'node:test';
import assert from 'node:assert/strict';
import {createGenerationQueue} from '../../lcalc_registry/static/generation-queue.mjs';

class Element {
  constructor(doc) { this.ownerDocument = doc; this.children = []; this.textContent = ''; this.disabled = false; this.open = false; }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = nodes; }
  removeAttribute(name) { delete this[name]; }
  showModal() { this.open = true; }
  close() { this.open = false; }
}
function setup(overrides = {}) {
  const doc = {createElement: () => new Element(doc)};
  const nodes = Object.fromEntries(['dialog', 'body', 'summary', 'progress', 'generateButton'].map(name => [name, new Element(doc)]));
  const errors = [];
  const queue = createGenerationQueue({
    ...nodes, submit: async () => [], getTask: async () => { throw Error('unexpected poll'); },
    onError: error => errors.push(error), pollMs: 5, ...overrides,
  });
  return {...nodes, queue, errors};
}
async function until(predicate) {
  for (let i = 0; i < 100 && !predicate(); i++) await new Promise(resolve => setTimeout(resolve, 5));
  assert.ok(predicate(), 'queue did not reach the expected state');
}

test('click immediately opens a submitting popup and blocks duplicate submissions', async () => {
  let finish;
  let posts = 0;
  const s = setup({submit: () => { posts++; return new Promise(resolve => { finish = resolve; }); }});
  const started = s.queue.start(['curve'], 'environment', new Map([['curve', '11.a1']]));
  try {
    assert.equal(s.dialog.open, true);
    assert.equal(s.generateButton.disabled, true);
    assert.match(s.summary.textContent, /Submitting 1 curve/);
    assert.equal(s.progress.value, undefined); // Indeterminate while submitting.
    await s.queue.start(['curve'], 'environment');
    assert.equal(posts, 1);
    finish([{id: 'job', curve_id: 'curve', status: 'pending'}]);
    await started;
    assert.equal(s.generateButton.disabled, false);
    assert.match(s.summary.textContent, /1 queued/);
    assert.equal(s.body.children[0].children[0].textContent, '11.a1');
  } finally { s.queue.dispose(); }
});

test('exact submitted jobs keep polling after closing; completion provides source links', async () => {
  const polled = [];
  let updates = 0;
  const s = setup({
    submit: async () => [{id: 'my-job', curve_id: 'curve', status: 'pending'}],
    getTask: async id => {
      polled.push(id);
      return {id, curve_id: 'curve', status: polled.length === 1 ? 'running' : 'succeeded', result: {proof_version_id: 'version'}};
    },
    onUpdate: async () => { updates++; },
  });
  try {
    await s.queue.start(['curve'], 'environment', new Map([['curve', '<img onerror=bad>']]));
    s.dialog.close();
    await until(() => s.summary.textContent.includes('1 candidates ready'));
    assert.equal(s.dialog.open, false);
    assert.deepEqual(polled, ['my-job', 'my-job']);
    assert.equal(s.progress.value, 1);
    assert.equal(s.progress.max, 1);
    assert.equal(s.body.children[0].children[0].textContent, '<img onerror=bad>');
    const details = s.body.children[0].children[2];
    assert.equal(details.children[1].href, '/v1/proof-versions/version/source');
    assert.ok(updates >= 2);
    s.queue.open();
    assert.equal(s.dialog.open, true);
  } finally { s.queue.dispose(); }
});

test('failed and inconclusive jobs display their error and count as finished', async () => {
  const s = setup({submit: async () => [
    {id: 'a', status: 'failed', error: 'Worker could not generate this witness'},
    {id: 'b', status: 'inconclusive', error: 'Numerical separation unavailable'},
  ]});
  try {
    await s.queue.start(['a', 'b'], 'environment');
    assert.match(s.summary.textContent, /1 failed · 1 inconclusive/);
    assert.equal(s.progress.value, 2);
    assert.equal(s.body.children[0].children[2].textContent, 'Worker could not generate this witness');
  } finally { s.queue.dispose(); }
});

test('submission errors stay visible inside the popup and allow retry', async () => {
  const s = setup({submit: async () => { throw Error('Unauthorized'); }});
  try {
    await s.queue.start(['curve'], 'environment');
    assert.equal(s.dialog.open, true);
    assert.match(s.summary.textContent, /Could not submit.*Unauthorized/);
    assert.equal(s.generateButton.disabled, false);
    assert.deepEqual(s.errors, ['Unauthorized']);
    assert.equal(s.body.children.length, 0);
  } finally { s.queue.dispose(); }
});

test('empty selection opens useful feedback without sending work', async () => {
  let posts = 0;
  const s = setup({submit: async () => { posts++; return []; }});
  try {
    await s.queue.start([], 'environment');
    assert.equal(posts, 0);
    assert.equal(s.dialog.open, true);
    assert.match(s.summary.textContent, /Select at least one curve/);
  } finally { s.queue.dispose(); }
});

test('multiple clicks accumulate only this page’s submitted jobs', async () => {
  let sequence = 0;
  const s = setup({submit: async () => [{id: String(++sequence), status: 'succeeded', curve_id: 'curve'}]});
  try {
    await s.queue.start(['curve'], 'env1', new Map([['curve', '11.a1']]));
    await s.queue.start(['curve'], 'env2', new Map([['curve', '37.a1']]));
    assert.equal(s.body.children.length, 2);
    assert.equal(s.body.children[0].children[0].textContent, '11.a1');
    assert.equal(s.body.children[1].children[0].textContent, '37.a1');
    assert.match(s.summary.textContent, /2 candidates ready/);
  } finally { s.queue.dispose(); }
});

test('temporary polling failure retries rather than abandoning queued work', async () => {
  let attempts = 0;
  const s = setup({
    submit: async () => [{id: 'retry', curve_id: 'curve', status: 'pending'}],
    getTask: async id => {
      if (++attempts === 1) throw Error('Temporarily unavailable');
      return {id, status: 'succeeded'};
    },
  });
  try {
    await s.queue.start(['curve'], 'environment');
    await until(() => s.summary.textContent.includes('1 candidates ready'));
    assert.equal(attempts, 2);
    assert.deepEqual(s.errors, ['Temporarily unavailable']);
  } finally { s.queue.dispose(); }
});

test('a refresh failure does not report an accepted submission as failed', async () => {
  const s = setup({
    submit: async () => [{id: 'accepted', status: 'succeeded'}],
    onUpdate: async () => { throw Error('Page refresh failed'); },
  });
  try {
    await s.queue.start(['curve'], 'environment');
    assert.match(s.summary.textContent, /Jobs were queued/);
    assert.equal(s.body.children.length, 1);
    assert.equal(s.generateButton.disabled, false);
  } finally { s.queue.dispose(); }
});
