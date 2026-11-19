/** Live checking progress takes display priority; historical acceptance is retained. */
export function verificationStatus(proof) {
  const state = proof.verification_status;
  const accepted = Boolean(proof.last_accepted_check) || proof.status === 'checked';
  const history = accepted ? ' · previously checked' : '';
  if (state === 'queued' || proof.status === 'queued') {
    return {label: 'Queued for verification' + history, active: true};
  }
  if (state === 'running' || proof.status === 'running') {
    return {label: 'Verification running' + history, active: true};
  }
  if (state === 'rejected' || state === 'timeout') {
    return {label: (state === 'timeout' ? 'Verification timed out' : 'Verification rejected') + history, active: false};
  }
  return {label: accepted ? 'Checked in this environment' : 'Unchecked candidate', active: false};
}
