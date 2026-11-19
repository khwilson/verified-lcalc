import test from 'node:test';
import assert from 'node:assert/strict';
import {verificationStatus} from '../../lcalc_registry/static/verification-status.mjs';

test('queued and running checks are visible and keep polling', () => {
  assert.deepEqual(verificationStatus({status: 'queued', verification_status: 'queued'}), {label: 'Queued for verification', active: true});
  assert.deepEqual(verificationStatus({status: 'running', verification_status: 'running'}), {label: 'Verification running', active: true});
});
test('rechecks show queue status while retaining historical acceptance', () => {
  const value = verificationStatus({status: 'queued', verification_status: 'queued', last_accepted_check: {}});
  assert.equal(value.active, true);
  assert.match(value.label, /Queued for verification · previously checked/);
});
test('finished checks stop polling and distinguish failure from unchecked output', () => {
  assert.deepEqual(verificationStatus({status: 'checked', verification_status: 'accepted'}), {label: 'Checked in this environment', active: false});
  assert.deepEqual(verificationStatus({status: 'candidate', verification_status: 'rejected'}), {label: 'Verification rejected', active: false});
  assert.deepEqual(verificationStatus({status: 'candidate', verification_status: 'timeout'}), {label: 'Verification timed out', active: false});
  assert.deepEqual(verificationStatus({status: 'candidate', verification_status: 'not_requested'}), {label: 'Unchecked candidate', active: false});
});
