import {summarizeTasks} from './task-status.mjs';

/** Track this page's submitted jobs by their exact IDs, independently of filters. */
export function createGenerationQueue({dialog, body, summary, progress, generateButton,
  submit, getTask, onUpdate = async () => {}, onError = () => {}, pollMs = 2000}) {
  const jobs = new Map();
  const doc = body.ownerDocument;
  let submitting = false;
  let disposed = false;
  let timer;
  let revision = 0;
  let polling;

  function open() {
    if (!dialog.open) dialog.showModal();
  }
  function render() {
    const rows = [...jobs.values()];
    body.replaceChildren();
    for (const {task, label} of rows) {
      const row = doc.createElement('tr');
      const detail = task.error || (task.status === 'pending' ? 'Waiting for a matching worker'
        : task.status === 'running' ? 'Generating witness and Lean source'
        : task.status === 'succeeded' ? 'Unchecked candidate ready' : '');
      for (const text of [label, task.status, detail]) {
        const cell = doc.createElement('td');
        cell.textContent = text;
        row.append(cell);
      }
      if (task.status === 'succeeded' && task.result?.proof_version_id) {
        const link = doc.createElement('a');
        link.textContent = 'View Lean source';
        link.href = `/v1/proof-versions/${encodeURIComponent(task.result.proof_version_id)}/source`;
        link.target = '_blank';
        link.rel = 'noopener';
        row.children[2].append(doc.createElement('br'), link);
      }
      body.append(row);
    }
    const state = summarizeTasks(rows.map(row => row.task));
    progress.max = Math.max(1, rows.length);
    progress.value = rows.length - state.counts.pending - state.counts.running;
    summary.textContent = state.text.replace(/ \(latest \d+ jobs\)/, '');
    return state.active;
  }
  function schedule() {
    clearTimeout(timer);
    if (!disposed) timer = setTimeout(() => poll(), pollMs);
  }
  async function poll() {
    if (disposed) return;
    if (polling) { schedule(); return; }
    // Avoid flooding the API/database when a visitor selects many curves.
    const active = [...jobs.entries()].filter(([, row]) => ['pending', 'running'].includes(row.task.status));
    const before = revision;
    let changed = false;
    const run = async () => {
      for (let i = 0; i < active.length; i += 8) {
        const values = await Promise.all(active.slice(i, i + 8).map(async ([id, row]) => {
          const task = await getTask(id);
          if (task.id !== id) throw Error('Queue response does not match the requested job');
          return {task, label: row.label};
        }));
        if (disposed) return;
        for (const row of values) {
          changed ||= jobs.get(row.task.id)?.task.status !== row.task.status;
          jobs.set(row.task.id, row);
        }
      }
    };
    polling = run();
    try {
      await polling;
      if (disposed) return;
      const remaining = submitting ? true : render();
      if (changed) await onUpdate();
      if (remaining || before !== revision) schedule();
    } catch (error) {
      if (!disposed) {
        summary.textContent = `Could not refresh your queue: ${error.message}. Retrying…`;
        onError(error.message);
        schedule();
      }
    } finally { polling = undefined; }
  }
  async function start(curveIds, environmentId, labels = new Map()) {
    if (submitting || disposed) return;
    open();
    if (!curveIds.length || !environmentId) {
      summary.textContent = 'Select at least one curve and an environment first.';
      return;
    }
    submitting = true;
    generateButton.disabled = true;
    summary.textContent = `Submitting ${curveIds.length} curve${curveIds.length === 1 ? '' : 's'} to your queue…`;
    progress.removeAttribute('value');
    let accepted = false;
    try {
      const tasks = await submit({curve_ids: curveIds, environment_id: environmentId});
      if (disposed) return;
      accepted = true;
      for (const task of tasks) jobs.set(task.id, {
        task, label: labels.get(task.curve_id) || task.curve_id?.slice(0, 12) || task.id,
      });
      revision++;
      render();
      schedule();
      await onUpdate();
    } catch (error) {
      if (!disposed) {
        render();
        summary.textContent = accepted
          ? `Jobs were queued, but the page could not refresh: ${error.message}`
          : `Could not submit generation request: ${error.message}`;
        onError(error.message);
      }
    } finally {
      submitting = false;
      generateButton.disabled = false;
    }
  }
  return {start, open, dispose() { disposed = true; clearTimeout(timer); }};
}
