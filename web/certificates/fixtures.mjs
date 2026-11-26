const repository = "https://github.com/khwilson/verified-lcalc";
const statusNames = {
  unconditional: "Unconditional",
  assumption_backed: "Uses elliptic modularity",
  conditional_fixture: "Requires a supplied realization",
  pending_review: "Awaiting fixture review",
  missing_checker: "No checker"
};

const search = document.getElementById("fixture-search");
const status = document.getElementById("fixture-status");
const count = document.getElementById("fixture-count");
const fields = document.getElementById("fixture-fields");

function node(tag, text) {
  const item = document.createElement(tag);
  if (text !== undefined) item.textContent = text;
  return item;
}

function sourceLink(text, revision, path, line) {
  const link = node("a", text);
  link.href = `${repository}/blob/${revision}/${path}${line ? `#L${line}` : ""}`;
  return link;
}

function evidenceDetails(proof, source, revision) {
  const details = node("details");
  const extent = proof.extent === "partial" ? " · Partial" : "";
  details.append(node("summary", `${proof.curve} · ${statusNames[proof.status]}${extent}`));
  details.append(node("p", proof.scope));
  const statement = node("pre");
  statement.append(node("code", proof.statement));
  details.append(statement);
  if (proof.project_axioms.length) {
    const assumptions = node("p", "Project axioms ");
    assumptions.append(node("code", proof.project_axioms.join(", ")));
    details.append(assumptions);
  }
  const links = node("p");
  links.className = "artifact-links";
  links.append(sourceLink(proof.theorem, revision, source, proof.proof_line),
    sourceLink("Fixture input", revision, proof.source));
  details.append(links);
  return details;
}

function fieldRow(field, source, revision) {
  const row = node("tr");
  const title = node("th");
  title.scope = "row";
  title.append(node("code", `${field.table}.${field.field}`));
  const evidence = node("td");
  if (field.evidence.length) {
    evidence.append(...field.evidence.map(proof => evidenceDetails(proof, source, revision)));
  } else {
    evidence.append(node("div", statusNames[field.status]));
    if (field.checker_scopes.length) {
      const checker = node("details");
      checker.append(node("summary", "Supported checker cases"));
      for (const scope of field.checker_scopes) checker.append(node("p", scope));
      evidence.append(checker);
    }
  }
  const scopes = [...field.report_only_scopes, ...field.metadata_scopes];
  if (scopes.length) {
    const notes = node("details");
    notes.append(node("summary", "Reports and metadata"));
    for (const scope of scopes) notes.append(node("p", scope));
    evidence.append(notes);
  }
  row.append(title, evidence);
  return row;
}

function render(report) {
  const query = search.value.trim().toLowerCase();
  const matches = report.fields.filter(field => {
    if (status.value && field.status !== status.value) return false;
    return `${field.table}.${field.field}`.toLowerCase().includes(query) ||
      field.evidence.some(proof => proof.curve.includes(query));
  });
  const revision = /^[0-9a-f]{40}$/.test(report.git_revision) ? report.git_revision : "main";
  fields.replaceChildren(...matches.map(field => fieldRow(field, report.proof_source, revision)));
  count.textContent = `${matches.length} of ${report.table_qualified_fields} table-qualified fields`;
  document.getElementById("fixture-results").hidden = matches.length === 0;
}

async function load() {
  const response = await fetch("fixture-field-coverage.json");
  if (!response.ok) throw new Error("Fixture report unavailable");
  const report = await response.json();
  if (report.schema !== "lcalc.fixture-field-coverage.v1") throw new Error("Unknown report format");
  render(report);
  document.getElementById("fixture-filters").disabled = false;
  search.addEventListener("input", () => render(report));
  status.addEventListener("change", () => render(report));
}

load().catch(() => {
  count.textContent = "Unable to load fixture evidence.";
  count.dataset.state = "warning";
});
