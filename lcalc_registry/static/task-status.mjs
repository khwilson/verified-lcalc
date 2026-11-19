/** Summarize generation outcomes without equating source generation with checking. */
export function summarizeTasks(tasks) {
  const counts = {pending: 0, running: 0, succeeded: 0, failed: 0, inconclusive: 0};
  for (const task of tasks) {
    if (Object.hasOwn(counts, task.status)) counts[task.status]++;
  }
  const active = counts.pending + counts.running > 0;
  let text = tasks.length
    ? `${counts.pending} queued · ${counts.running} running · ${counts.succeeded} candidates ready · ${counts.failed} failed · ${counts.inconclusive} inconclusive (latest ${tasks.length} jobs).`
    : 'No generation jobs for this source and environment.';
  if (counts.pending && !counts.running) text += ' Waiting for a matching worker; check its terminal if this persists.';
  text += ' Generation does not perform kernel verification.';
  return {active, counts, text};
}
