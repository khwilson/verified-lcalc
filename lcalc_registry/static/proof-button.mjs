/** Mount an LMFDB proof request button. By default the server searches for a witness.
 * Optional getWitness() supplies numerical JSON instead. Neither path runs a kernel check.
 * Returns a cleanup callback; already queued server work continues after cleanup.
 */
export function mountProofButton(container, {api, sourceId, label, environmentId, getWitness}) {
  const base = new URL(api);
  if (base.protocol !== 'https:' && !(base.protocol === 'http:' &&
      ['localhost', '127.0.0.1', '[::1]'].includes(base.hostname))) {
    throw new Error('Proof API must use HTTPS (or local HTTP for development)');
  }
  const doc = container.ownerDocument;
  const button = doc.createElement('button');
  button.type = 'button';
  button.textContent = 'Generate a Lean proof candidate';
  const status = doc.createElement('span');
  status.setAttribute('role', 'status');
  status.setAttribute('aria-live', 'polite');
  const download = doc.createElement('a');
  download.textContent = 'Download unchecked Lean proof';
  download.hidden = true;
  container.append(button, status, download);
  const controller = new AbortController();
  let timer;
  let disposed = false;
  async function request(path, options = {}) {
    const response = await fetch(new URL(path, base), {
      ...options, credentials: 'omit', signal: controller.signal,
    });
    const value = await response.json();
    if (!response.ok) throw new Error(value.detail || `Request failed (${response.status})`);
    return value;
  }
  function fail(error) {
    if (disposed) return;
    status.textContent = ` ${error.message}`;
    button.disabled = false;
  }
  async function poll(id) {
    try {
      const value = await request(`/v1/proof-requests/${encodeURIComponent(id)}`);
      if (disposed) return;
      if (value.status === 'succeeded') {
        // Construct the link locally; do not trust a response-supplied cross-origin URL.
        download.href = new URL(`/v1/proof-requests/${encodeURIComponent(id)}/bundle`, base).href;
        download.hidden = false;
        status.textContent = ' Ready: unchecked candidate. Check it with Lean before relying on it. ';
        button.disabled = false;
      } else if (['failed', 'inconclusive'].includes(value.status)) {
        throw new Error(value.error || 'No proof candidate available for this curve.');
      } else {
        status.textContent = ' Queued or generating; kernel verification has not been requested.';
        timer = setTimeout(() => poll(id), 1500);
      }
    } catch (error) { fail(error); }
  }
  button.addEventListener('click', async () => {
    button.disabled = true;
    download.hidden = true;
    status.textContent = getWitness ? ' Preparing a numerical witness…' : ' Requesting server witness search…';
    try {
      const body = {source_id: sourceId, label, environment_id: environmentId};
      if (getWitness) {
        body.witness = await getWitness();
        if (!body.witness || typeof body.witness !== 'object' || Array.isArray(body.witness)) {
          throw new Error('The witness callback must return a numerical witness object');
        }
      }
      if (disposed) return;
      const value = await request('/v1/proof-requests', {
        method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body),
      });
      if (!disposed) await poll(value.id);
    } catch (error) { fail(error); }
  });
  return () => {
    disposed = true;
    clearTimeout(timer);
    controller.abort();
    button.disabled = true;
  };
}
