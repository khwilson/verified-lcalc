import test from 'node:test';
import assert from 'node:assert/strict';
import {summarizeTasks} from '../../lcalc_registry/static/task-status.mjs';

test('queued work stays active and explains waiting for a matching worker', () => {
  const value = summarizeTasks([{status: 'pending'}]);
  assert.equal(value.active, true);
  assert.match(value.text, /Waiting for a matching worker/);
  assert.match(value.text, /does not perform kernel verification/);
});
test('running work and failures are distinguishable from ready candidates', () => {
  const value = summarizeTasks(['pending', 'running', 'succeeded', 'failed', 'inconclusive'].map(status => ({status})));
  assert.deepEqual(value.counts, {pending: 1, running: 1, succeeded: 1, failed: 1, inconclusive: 1});
  assert.equal(value.active, true);
  assert.doesNotMatch(value.text, /Waiting for/);
});
test('terminal and empty queues stop polling', () => {
  assert.equal(summarizeTasks([]).active, false);
  const value = summarizeTasks([{status: 'succeeded'}, {status: 'failed'}, {status: 'inconclusive'}]);
  assert.equal(value.active, false);
  assert.match(value.text, /1 candidates ready/);
});
