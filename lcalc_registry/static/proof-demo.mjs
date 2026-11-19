import {mountProofButton} from './proof-button.mjs';
const params = new URL(location.href).searchParams;
const sourceId = params.get('source_id');
const label = params.get('label');
const environmentId = params.get('environment_id');
const subject = document.getElementById('subject');
if (!sourceId || !label || !environmentId) {
  subject.textContent = 'Supply source_id, label, and environment_id query parameters for a registered snapshot and checker.';
} else {
  subject.textContent = `Curve: ${label}`;
  const stop = mountProofButton(document.getElementById('proof'), {
    api: location.origin, sourceId, label, environmentId,
  });
  window.addEventListener('pagehide', stop, {once: true});
}
