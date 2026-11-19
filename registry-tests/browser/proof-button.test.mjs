import test from 'node:test';
import assert from 'node:assert/strict';
import {mountProofButton} from '../../lcalc_registry/static/proof-button.mjs';

class Element {
  constructor(doc) { this.ownerDocument = doc; this.children = []; this.listeners = {}; }
  append(...elements) { this.children.push(...elements); }
  setAttribute() {}
  addEventListener(name, callback) { this.listeners[name] = callback; }
}
function container() {
  const doc = {createElement: () => new Element(doc)};
  return new Element(doc);
}
const options = {api: 'https://proofs.example.org', sourceId: 'snapshot', label: '<img onerror=alert(1)>', environmentId: 'env'};

for (const supplied of [false, true]) {
  test(`button opt-in, ${supplied ? 'supplied witness' : 'server search'}, unchecked download`, async () => {
    const calls = [];
    globalThis.fetch = async (url, init) => {
      calls.push({url: url.href, init});
      assert.equal(init.credentials, 'omit');
      if (init.method === 'POST') {
        const body = JSON.parse(init.body);
        assert.equal(body.label, options.label);
        assert.equal(Object.hasOwn(body, 'witness'), supplied);
        assert.ok(!Object.hasOwn(body, 'verify'));
        return {ok: true, json: async () => ({id: 'proof-request-example'})};
      }
      return {ok: true, json: async () => ({status: 'succeeded', bundle_url: 'https://malicious.invalid'})};
    };
    const root = container();
    let computed = 0;
    const stop = mountProofButton(root, {...options, ...(supplied ? {getWitness: async () => {
      computed++;
      return {schema: 'lcalc.ec-rank.v1'};
    }} : {})});
    assert.equal(calls.length, 0);
    assert.equal(computed, 0);
    const [button, status, link] = root.children;
    await button.listeners.click();
    assert.equal(calls.length, 2);
    assert.equal(computed, supplied ? 1 : 0);
    assert.equal(link.href, 'https://proofs.example.org/v1/proof-requests/proof-request-example/bundle');
    assert.equal(link.hidden, false);
    assert.match(status.textContent, /unchecked/);
    assert.equal(button.disabled, false);
    stop();
    assert.equal(button.disabled, true);
  });
}

test('queue failure stays an error, never a checked result', async () => {
  globalThis.fetch = async () => ({ok: false, status: 429, json: async () => ({detail: 'Queue full'})});
  const root = container();
  const stop = mountProofButton(root, options);
  const [button, status, link] = root.children;
  await button.listeners.click();
  assert.match(status.textContent, /Queue full/);
  assert.equal(link.hidden, true);
  assert.equal(button.disabled, false);
  stop();
});

test('cleanup cancels polling without queuing additional work', async () => {
  let calls = 0;
  globalThis.fetch = async () => {
    calls++;
    return {ok: true, json: async () => calls === 1 ? {id: 'id'} : {status: 'running'}};
  };
  const root = container();
  const stop = mountProofButton(root, options);
  await root.children[0].listeners.click();
  stop();
  assert.equal(calls, 2);
});

test('remote HTTP is rejected', () => {
  assert.throws(() => mountProofButton(container(), {...options, api: 'http://proofs.example.org'}), /HTTPS/);
});

test('invalid witness callback cannot silently fall back to server search', async () => {
  let called = false;
  globalThis.fetch = async () => { called = true; throw new Error('unexpected'); };
  const root = container();
  const stop = mountProofButton(root, {...options, getWitness: async () => null});
  await root.children[0].listeners.click();
  assert.equal(called, false);
  assert.match(root.children[1].textContent, /must return/);
  stop();
});
