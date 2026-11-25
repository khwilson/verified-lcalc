const repository = "https://github.com/khwilson/verified-lcalc";
const labelPattern = /^(\d+)\.([a-z]+)(\d+)$/;
const cataloguePattern = /^ec-certificates-\d+-\d+\.json$/;
const collator = new Intl.Collator("en", {numeric: true});
const formatCount = new Intl.NumberFormat();
const pageSize = 40;

const elements = Object.fromEntries(
  ["filters", "search", "status", "rank", "clear", "notice", "results",
    "result-count", "curves", "previous", "next", "page"].map(
    id => [id, document.getElementById(id)]
  )
);
let records = [];
let page = 0;
let activeLabel = new URL(location.href).searchParams.get("curve")?.toLowerCase() || "";
elements.search.value = activeLabel;

function node(tag, text, options = {}) {
  const result = document.createElement(tag);
  if (text !== undefined) result.textContent = text;
  for (const [attribute, value] of Object.entries(options)) {
    result.setAttribute(attribute, value);
  }
  return result;
}

function link(text, href, options = {}) {
  return node("a", text, {href, ...options});
}

function lmfdbUrl(label) {
  const [, conductor, isogenyClass, number] = labelPattern.exec(label);
  return `https://www.lmfdb.org/EllipticCurve/Q/${conductor}/${isogenyClass}/${number}`;
}

function artifactUrl(path) {
  if (typeof path !== "string" || !path) return null;
  try {
    const url = new URL(path, document.baseURI);
    return url.protocol === "https:" || (url.protocol === "http:" && url.origin === location.origin)
      ? url.href
      : null;
  } catch {
    return null;
  }
}

function definition(list, title, content) {
  const value = node("dd");
  value.append(content);
  list.append(node("dt", title), value);
}

function metadata(list, catalogue) {
  const {git_revision: revision, toolchain, mathlib_revision, tauceti_revision} = catalogue;
  if (revision) {
    definition(list, "Git revision", /^[0-9a-f]{7,40}$/.test(revision)
      ? link(revision, `${repository}/tree/${revision}`)
      : node("code", revision));
  }
  if (toolchain) definition(list, "Lean toolchain", node("code", toolchain));
  if (mathlib_revision) definition(list, "Mathlib revision", node("code", mathlib_revision));
  if (tauceti_revision) definition(list, "TauCeti revision", node("code", tauceti_revision));
}

function factHeading(fact) {
  switch (fact.field) {
    case "analytic_rank": return `Exact analytic rank ${fact.value}`;
    case "nonsingular": return "Nonsingular (Δ ≠ 0)";
    case "global_minimal": return "Globally minimal integral equation";
    default: return `${fact.field} = ${fact.value}`;
  }
}

function factDetails({fact, catalogue}, curveLabel) {
  const article = node("article");
  const list = node("dl");
  article.append(node("h3", factHeading(fact)), list);
  definition(list, "Lean theorem", node("code", fact.theorem));
  definition(list, "Lean module", node("code", fact.module));
  const assumptions = node("ul");
  for (const assumption of fact.assumptions) {
    const item = node("li");
    item.append(node("code", assumption));
    assumptions.append(item);
  }
  definition(list, "Project assumptions", assumptions.childElementCount ? assumptions : "None");
  metadata(list, catalogue);
  if (fact.sha256) definition(list, ".olean SHA-256", node("code", fact.sha256));
  const downloads = node("div", undefined, {class: "artifact-links"});
  const olean = artifactUrl(fact.olean_url);
  const bundle = artifactUrl(fact.bundle_url);
  if (olean) downloads.append(link("Download .olean", olean));
  if (bundle) downloads.append(link("Download module bundle", bundle));
  if (downloads.childElementCount) article.append(downloads);
  article.setAttribute("aria-label", `${curveLabel} · ${factHeading(fact)}`);
  return article;
}

function analyticRank(record) {
  return record.facts.get("analytic_rank")?.fact.value;
}

function rowsFor(record) {
  const {row, catalogue, facts} = record;
  const open = row.label === activeLabel;
  const tr = node("tr");
  const curve = node("th", undefined, {scope: "row"});
  curve.append(link(row.label, lmfdbUrl(row.label), {
    class: "curve-link", "aria-label": `${row.label} on LMFDB`
  }));
  const status = node("td");
  status.append(node("span", row.status === "checked" ? `${facts.size} verified facts` : "Inconclusive", {
    class: "status", "data-status": row.status
  }));
  const control = node("td");
  const detailId = `detail-${row.label}`;
  const button = node("button", open ? "Hide" : "Details", {
    type: "button", class: "detail-button", "aria-expanded": String(open),
    "aria-controls": detailId, "aria-label": `${open ? "Hide" : "Show"} details for ${row.label}`
  });
  button.addEventListener("click", () => {
    updateDeepLink(open ? "" : row.label);
    render();
    document.getElementById(`toggle-${row.label}`)?.focus();
  });
  button.id = `toggle-${row.label}`;
  control.append(button);
  tr.append(curve, node("td", row.conductor), status, node("td", analyticRank(record) ?? "—"), control);

  const detailRow = node("tr", undefined, {class: "detail-row", id: detailId});
  detailRow.hidden = !open;
  const cell = node("td", undefined, {colspan: "5"});
  detailRow.append(cell);
  if (open) {
    const detail = node("div", undefined, {class: "detail"});
    cell.append(detail);
    if (Array.isArray(row.ainvs) && row.ainvs.length === 5) {
      const equation = node("p");
      equation.append("Integral coefficients ", node("code", `[${row.ainvs.join(", ")}]`));
      detail.append(equation);
    }
    if (facts.size) {
      const tag = catalogue.batch?.release_tag;
      const archive = artifactUrl(catalogue.witness_archive?.url);
      if (archive && /^ec-certificates-\d+-\d+$/.test(tag)) {
        const replay = node("div", undefined, {class: "artifact-links"});
        replay.append(link("Download exact witnesses", archive),
          link("Batch catalog", `${repository}/releases/download/${tag}/catalog.json`),
          link("Signed provenance", `${repository}/releases/download/${tag}/provenance.sigstore.json`),
          link("Verify and replay", `${repository}/blob/${catalogue.git_revision}/docs/CERTIFIED_ARTIFACTS.md`));
        detail.append(replay);
        if (row.witness_sha256) {
          const witness = node("dl");
          definition(witness, "Witness SHA-256", node("code", row.witness_sha256));
          detail.append(witness);
        }
      }
      for (const evidence of facts.values()) detail.append(factDetails(evidence, row.label));
    } else {
      detail.append(node("h3", `${row.label} · Inconclusive`));
      if (row.reason) detail.append(node("p", row.reason));
      const list = node("dl");
      metadata(list, catalogue);
      detail.append(list);
    }
  }
  return [tr, detailRow];
}

function updateDeepLink(label) {
  activeLabel = label;
  const url = new URL(location.href);
  if (label) url.searchParams.set("curve", label);
  else url.searchParams.delete("curve");
  history.replaceState(null, "", url);
}

function matchingRecords() {
  const query = elements.search.value.trim().toLowerCase();
  const status = elements.status.value;
  const rank = elements.rank.value;
  return records.filter(record =>
    record.row.label.includes(query) &&
    (!status || record.row.status === status) &&
    (!rank || String(analyticRank(record)) === rank)
  );
}

function render() {
  const matches = matchingRecords();
  const pages = Math.ceil(matches.length / pageSize);
  page = Math.min(page, Math.max(0, pages - 1));
  const start = page * pageSize;
  const count = formatCount.format(matches.length);
  const total = formatCount.format(records.length);
  elements["result-count"].textContent = matches.length
    ? `Showing ${formatCount.format(start + 1)}–${formatCount.format(Math.min(start + pageSize, matches.length))} of ${count} matches · ${total} curves in catalogue`
    : "No curves match these filters.";
  elements.curves.replaceChildren(...matches.slice(start, start + pageSize).flatMap(rowsFor));
  elements.curves.closest(".table-wrap").hidden = !matches.length;
  elements.page.textContent = `Page ${formatCount.format(page + 1)} of ${formatCount.format(pages)}`;
  elements.previous.disabled = page === 0;
  elements.next.disabled = page + 1 >= pages;
  elements.page.closest("nav").hidden = pages < 2;
  elements.results.hidden = false;
}

function updateFilters() {
  page = 0;
  if (activeLabel && !matchingRecords().some(({row}) => row.label === activeLabel)) {
    updateDeepLink("");
  }
  render();
}

elements.search.addEventListener("input", updateFilters);
elements.status.addEventListener("change", updateFilters);
elements.rank.addEventListener("change", updateFilters);
elements.clear.addEventListener("click", () => {
  elements.search.value = elements.status.value = elements.rank.value = "";
  updateDeepLink("");
  updateFilters();
  elements.search.focus();
});
elements.previous.addEventListener("click", () => { page -= 1; render(); });
elements.next.addEventListener("click", () => { page += 1; render(); });

async function getJson(url) {
  const response = await fetch(url, {cache: "no-cache"});
  if (!response.ok) throw new Error(`HTTP ${response.status}`);
  return response.json();
}

function validateCatalogue(catalogue) {
  const validFact = fact => fact && typeof fact.field === "string" &&
    typeof fact.theorem === "string" && typeof fact.module === "string" &&
    Array.isArray(fact.assumptions) && fact.assumptions.every(a => typeof a === "string");
  if (catalogue?.schema !== 1 || !Array.isArray(catalogue.curves) ||
    !catalogue.curves.every(row => row && labelPattern.test(row.label) &&
      ["checked", "inconclusive"].includes(row.status) && Array.isArray(row.facts) &&
      (row.status === "checked" ? row.facts.length > 0 && row.facts.every(validFact) : !row.facts.length)
    )) {
    throw new Error("Unsupported catalogue structure");
  }
  return catalogue;
}

function mergeCatalogue(byLabel, catalogue) {
  for (const row of catalogue.curves) {
    let record = byLabel.get(row.label);
    if (record && (record.row.conductor !== row.conductor ||
        JSON.stringify(record.row.ainvs) !== JSON.stringify(row.ainvs))) continue;
    if (!record || (record.row.status === "inconclusive" && row.status === "checked")) {
      record = {row, catalogue, facts: new Map()};
      byLabel.set(row.label, record);
    }
    for (const fact of row.facts) {
      if (!record.facts.has(fact.field)) record.facts.set(fact.field, {fact, catalogue});
    }
  }
}

function notice(text, warning = false) {
  elements.notice.textContent = text;
  elements.notice.hidden = !text;
  elements.notice.dataset.state = warning ? "warning" : "";
}

async function load() {
  try {
    const index = await getJson("catalogs/index.json");
    if (!Array.isArray(index) || index.some(name => typeof name !== "string" || !cataloguePattern.test(name))) {
      throw new Error("Unsupported catalogue index");
    }
    const filenames = Array.from(new Set(index));
    const byLabel = new Map();
    let failed = 0;
    for (let i = 0; i < filenames.length; i += 6) {
      const group = await Promise.allSettled(filenames.slice(i, i + 6).map(async name =>
        validateCatalogue(await getJson(`catalogs/${name}`))
      ));
      for (const result of group) {
        if (result.status === "fulfilled") mergeCatalogue(byLabel, result.value);
        else failed += 1;
      }
    }
    if (filenames.length && failed === filenames.length) {
      notice("The index loaded, but its certificate catalogues are unavailable. Try again later.", true);
      return;
    }
    records = [...byLabel.values()].sort((a, b) => collator.compare(a.row.label, b.row.label));
    if (!records.length) {
      notice(failed ? "Some catalogues are unavailable. No curve records could be loaded." :
        "No certificate results have been published yet.", Boolean(failed));
      return;
    }
    notice(failed ? `${failed} of ${filenames.length} catalogues could not be loaded. Showing available results.` : "", Boolean(failed));
    elements.filters.disabled = false;
    const exact = matchingRecords().findIndex(({row}) => row.label === activeLabel);
    if (exact >= 0) page = Math.floor(exact / pageSize);
    render();
    if (exact >= 0) document.getElementById(`detail-${activeLabel}`)?.scrollIntoView({block: "nearest"});
  } catch {
    notice("The certificate catalogue index could not be loaded. Try again later.", true);
  }
}

load();
