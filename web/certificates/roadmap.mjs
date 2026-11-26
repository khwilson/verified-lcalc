const repository = "https://github.com/khwilson/verified-lcalc";
const graphPath = "field-dependency-roadmap.json";
const search = document.getElementById("search");
const tableFilter = document.getElementById("table-filter");
const statusFilter = document.getElementById("status-filter");
const blockerFilter = document.getElementById("blocker-filter");
const fieldList = document.getElementById("field-list");
const loadStatus = document.getElementById("load-status");
let graph;
let nodeById;
let incoming;
let outgoing;
let selectedId = null;
let selectedWave = "";
let redrawGraph = () => {};
let graphResizeObserver = null;

function element(tag, text) {
  const item = document.createElement(tag);
  if (text !== undefined && text !== null) item.textContent = String(text);
  return item;
}

function asText(value) {
  if (value === null || value === undefined || value === "") return "Not supplied";
  if (typeof value === "string") return value;
  if (typeof value === "number" || typeof value === "boolean") return String(value);
  return JSON.stringify(value, null, 2);
}

function makeBadge(text, status = "") {
  const badge = element("span", text || "unknown");
  badge.className = "badge";
  badge.dataset.status = status || String(text || "").toLowerCase();
  return badge;
}

function statusLabel(status) {
  const labels = {
    current: "Current",
    planned_or_partial: "Planned / partial",
    sampled: "Proof sample",
    pending_review: "Needs review",
    missing_checker: "No checker",
    specified: "Specified",
    scoped: "Scoped",
    defined: "Defined",
    implemented: "Implemented",
    missing: "No generator route",
    scoped_checker: "Scoped checker",
    scoped_report: "Scoped report",
    not_reported: "No replay report",
    report_only: "Report only",
    checked_fixture_example: "Checked example",
    report_without_checked_fact: "Report only",
    checked: "Checked",
    not_run: "Not run",
    unsupported: "Unsupported",
    not_sampled: "Not sampled",
    not_supplied: "Not supplied",
    catalogued: "Catalogued",
    producer_dispatch: "Producer dispatch",
    unsupported_table_field: "No field dispatch",
    table_not_dispatched: "No table dispatch",
    claim_candidate: "Candidate route",
    local_claim_candidate: "Candidate local route",
    galrep_conductor_candidate: "Candidate Galois route",
    missing_components: "Missing components"
  };
  return labels[status] || String(status || "Unknown").replaceAll("_", " ");
}

function sourceLink(label, path, line) {
  const link = element("a", label);
  const candidateRevision = graph.git_revision || graph.generated_from?.git_revision;
  const revision = /^[0-9a-f]{40}$/.test(candidateRevision || "") ? candidateRevision : "main";
  link.href = `${repository}/blob/${revision}/${path}${line ? `#L${line}` : ""}`;
  link.rel = "noreferrer";
  return link;
}

function modulePath(moduleName) {
  return moduleName ? `${moduleName.replaceAll(".", "/")}.lean` : null;
}

function nodeButton(id, current = false, edge = null) {
  const node = nodeById.get(id);
  const button = element("button");
  button.type = "button";
  button.className = "node-button";
  button.dataset.nodeId = id;
  button.setAttribute("aria-current", current ? "true" : "false");
  button.setAttribute("aria-label", `${node.label || id}, status ${statusLabel(node.status)}${edge?.reason ? `, ${edge.reason}` : ""}`);
  const copy = element("span");
  copy.className = "node-copy";
  const label = element("span", node.label || id);
  label.className = "node-label";
  copy.append(label);
  if (edge?.reason || edge?.kind) {
    const context = element("small", [edge.kind, edge.reason].filter(Boolean).join(" · "));
    context.className = "edge-context";
    copy.append(context);
  }
  const status = element("span", statusLabel(node.status));
  status.className = "node-status";
  button.append(copy, status);
  button.addEventListener("click", () => selectNode(id, true));
  return button;
}

function valuesForSearch(node) {
  return JSON.stringify(node).toLowerCase();
}

function isBlocked(node) {
  const blocker = node.blocker || {};
  return Boolean(blocker.code && !["complete", "ready", "none"].includes(blocker.code));
}

function filteredNodes() {
  const query = search.value.trim().toLowerCase();
  return graph.nodes.filter(node => node.node_type === "field").filter(node => {
    if (selectedWave && node.wave !== selectedWave) return false;
    if (tableFilter.value && node.table !== tableFilter.value) return false;
    if (statusFilter.value && node.status !== statusFilter.value) return false;
    if (blockerFilter.checked && !isBlocked(node)) return false;
    return !query || valuesForSearch(node).includes(query);
  });
}

function renderFieldList() {
  const visible = filteredNodes();
  const totalFields = graph.nodes.filter(node => node.node_type === "field").length;
  document.getElementById("field-count").textContent = `${visible.length} of ${totalFields}`;
  fieldList.replaceChildren();
  if (!visible.length) {
    const empty = element("li", "No fields match these filters.");
    empty.className = "no-results";
    fieldList.append(empty);
    return;
  }
  for (const node of visible) {
    const item = element("li");
    item.append(nodeButton(node.id, node.id === selectedId));
    fieldList.append(item);
  }
}

function renderWaveOverview() {
  const waves = graph.waves || graph.nodes.filter(node => node.node_type === "milestone");
  const cards = document.getElementById("wave-cards");
  const scheduleLinks = document.getElementById("schedule-links");
  cards.replaceChildren();
  scheduleLinks.replaceChildren();
  const milestoneIds = new Set(waves.map(wave => wave.id));
  const prerequisiteEdges = graph.edges.filter(edge => milestoneIds.has(edge.from) && milestoneIds.has(edge.to));
  const grouped = new Map();
  for (const wave of waves) {
    const depth = Number.isInteger(wave.dependency_layer) ? wave.dependency_layer : 0;
    if (!grouped.has(depth)) grouped.set(depth, []);
    grouped.get(depth).push(wave);
  }
  const orderedGroups = [...grouped.entries()].sort((a, b) => a[0] - b[0]);
  cards.style.setProperty("--layer-template", orderedGroups
    .map(([, group]) => `${Math.max(1, Math.ceil(group.length / 4))}fr`).join(" "));
  for (const [depth, group] of orderedGroups) {
    const column = element("section");
    column.className = "wave-layer";
    column.setAttribute("aria-labelledby", `prereq-wave-${depth + 1}`);
    const heading = element("h3", `Layer ${depth + 1}`);
    heading.id = `prereq-wave-${depth + 1}`;
    column.append(heading);
    const packageCards = element("div");
    packageCards.className = "wave-package-list";
    for (const wave of group) {
      const parents = prerequisiteEdges.filter(edge => edge.to === wave.id).map(edge => nodeById.get(edge.from)?.wave).filter(Boolean);
      const children = prerequisiteEdges.filter(edge => edge.from === wave.id).map(edge => nodeById.get(edge.to)?.wave).filter(Boolean);
      const button = element("button");
      button.type = "button";
      button.className = "wave-card";
      button.dataset.wave = wave.wave;
      button.dataset.nodeId = wave.id;
      button.dataset.status = wave.status || "unknown";
      button.setAttribute("aria-pressed", selectedWave === wave.wave ? "true" : "false");
      const description = [
        `${wave.wave}: ${wave.label}`,
        `status ${statusLabel(wave.status)}`,
        parents.length ? `prerequisites ${parents.join(", ")}` : "no package prerequisite",
        children.length ? `unlocks ${children.join(", ")}` : "no package dependents"
      ].join(". ");
      button.setAttribute("aria-label", `${description}. Select to filter its fields.`);
      const id = element("span", wave.wave);
      id.className = "wave-card-title";
      const label = element("span", wave.label);
      label.className = "wave-card-label";
      const count = wave.field_count ?? wave.field_ids?.length ??
        graph.nodes.filter(node => node.node_type === "field" && node.wave === wave.wave).length;
      const meta = element("span");
      meta.className = "wave-card-meta";
      meta.append(element("span", `${count} fields`));
      const status = element("span", statusLabel(wave.status));
      status.className = "wave-card-status";
      status.dataset.status = wave.status || "unknown";
      meta.append(status);
      button.append(id, label, meta);
      button.addEventListener("click", () => {
        selectedWave = selectedWave === wave.wave ? "" : wave.wave;
        renderWaveOverview();
        renderFieldList();
        if (selectedWave) {
          const first = graph.nodes.find(node => node.node_type === "field" && node.wave === selectedWave);
          if (first) selectNode(first.id, true);
        }
      });
      packageCards.append(button);
    }
    column.append(packageCards);
    cards.append(column);
  }

  for (const edge of graph.scheduling_edges || []) {
    const from = nodeById.get(edge.from);
    const to = nodeById.get(edge.to);
    if (!from || !to) continue;
    const item = element("li");
    const button = element("button", `${from.wave} → ${to.wave} · ${edge.reason || "Implementation ordering only."}`);
    button.type = "button";
    button.className = "schedule-link";
    button.setAttribute("aria-label", `${from.wave} to ${to.wave}. Implementation scheduling only; not a proof prerequisite.`);
    button.addEventListener("click", () => selectNode(to.id, true));
    item.append(button);
    scheduleLinks.append(item);
  }
  if (!scheduleLinks.childElementCount) scheduleLinks.append(element("li", "No implementation-order notes supplied."));
  document.getElementById("all-waves").setAttribute("aria-pressed", selectedWave ? "false" : "true");
  const description = prerequisiteEdges.map(edge => {
    const from = nodeById.get(edge.from);
    const to = nodeById.get(edge.to);
    return `${from?.wave} prerequisite for ${to?.wave}: ${edge.reason}`;
  });
  document.getElementById("wave-graph-description").textContent = description.join(". ");
  requestAnimationFrame(() => redrawGraph());
}

function edgeItems(list, edges, emptyText) {
  list.replaceChildren();
  if (!edges.length) {
    const empty = element("li", emptyText);
    empty.className = "no-results";
    list.append(empty);
    return;
  }
  for (const edge of edges) {
    const item = element("li");
    item.append(nodeButton(edge.id, false, edge));
    list.append(item);
  }
}

function drawSvgEdges(svgId, containerId, edges, activeId = "", activeWave = "") {
  const svg = document.getElementById(svgId);
  const container = document.getElementById(containerId);
  if (!svg || !container) return;
  const bounds = container.getBoundingClientRect();
  const width = bounds.width;
  const height = bounds.height;
  if (!width || !height) return;
  const namespace = "http://www.w3.org/2000/svg";
  svg.replaceChildren();
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  svg.setAttribute("width", String(width));
  svg.setAttribute("height", String(height));
  const defs = document.createElementNS(namespace, "defs");
  const marker = document.createElementNS(namespace, "marker");
  const markerId = `${svgId}-arrow`;
  marker.setAttribute("id", markerId);
  marker.setAttribute("viewBox", "0 0 10 10");
  marker.setAttribute("refX", "8");
  marker.setAttribute("refY", "5");
  marker.setAttribute("markerWidth", "5");
  marker.setAttribute("markerHeight", "5");
  marker.setAttribute("orient", "auto-start-reverse");
  const arrow = document.createElementNS(namespace, "path");
  arrow.setAttribute("d", "M 0 0 L 10 5 L 0 10 z");
  arrow.setAttribute("fill", "#7389a5");
  marker.append(arrow);
  defs.append(marker);
  const activeMarker = marker.cloneNode(true);
  activeMarker.setAttribute("id", `${markerId}-active`);
  activeMarker.querySelector("path").setAttribute("fill", "#174d96");
  defs.append(activeMarker);
  svg.append(defs);

  const buttons = [...container.querySelectorAll("button[data-node-id]")];
  const buttonFor = id => buttons.find(button => button.dataset.nodeId === id);
  for (const edge of edges) {
    const fromButton = buttonFor(edge.from);
    const toButton = buttonFor(edge.to);
    if (!fromButton || !toButton) continue;
    const from = fromButton.getBoundingClientRect();
    const to = toButton.getBoundingClientRect();
    const fromCenter = { x: from.left + from.width / 2, y: from.top + from.height / 2 };
    const toCenter = { x: to.left + to.width / 2, y: to.top + to.height / 2 };
    let start;
    let end;
    if (Math.abs(toCenter.x - fromCenter.x) >= Math.abs(toCenter.y - fromCenter.y)) {
      start = { x: toCenter.x >= fromCenter.x ? from.right : from.left, y: fromCenter.y };
      end = { x: toCenter.x >= fromCenter.x ? to.left : to.right, y: toCenter.y };
    } else {
      start = { x: fromCenter.x, y: toCenter.y >= fromCenter.y ? from.bottom : from.top };
      end = { x: toCenter.x, y: toCenter.y >= fromCenter.y ? to.top : to.bottom };
    }
    start.x -= bounds.left;
    start.y -= bounds.top;
    end.x -= bounds.left;
    end.y -= bounds.top;
    const dx = end.x - start.x;
    const dy = end.y - start.y;
    const path = document.createElementNS(namespace, "path");
    path.setAttribute("d", `M ${start.x} ${start.y} C ${start.x + dx * .38} ${start.y + dy * .14}, ${end.x - dx * .38} ${end.y - dy * .14}, ${end.x} ${end.y}`);
    const active = edge.from === activeId || edge.to === activeId ||
      (activeWave && [edge.from, edge.to].some(id => nodeById.get(id)?.wave === activeWave));
    path.setAttribute("marker-end", `url(#${active ? `${markerId}-active` : markerId})`);
    path.setAttribute("class", active ? "graph-edge is-active" : "graph-edge");
    const title = document.createElementNS(namespace, "title");
    title.textContent = `${edge.from} → ${edge.to}${edge.reason ? `: ${edge.reason}` : ""}`;
    path.append(title);
    svg.append(path);
  }
}

function redrawAllGraphs() {
  const waves = graph.waves || graph.nodes.filter(node => node.node_type === "milestone");
  const waveIds = new Set(waves.map(wave => wave.id));
  const packageEdges = graph.edges.filter(edge => waveIds.has(edge.from) && waveIds.has(edge.to));
  drawSvgEdges("wave-svg", "wave-dag", packageEdges, selectedId, selectedWave);
  const selectedEdges = [
    ...(incoming.get(selectedId) || []).map(edge => ({ from: edge.from, to: selectedId })),
    ...(outgoing.get(selectedId) || []).map(edge => ({ from: selectedId, to: edge.to }))
  ];
  drawSvgEdges("selected-dag-svg", "dag", selectedEdges, selectedId);
}

function installGraphResizeObserver() {
  const redraw = () => requestAnimationFrame(() => redrawGraph());
  window.addEventListener("resize", redraw);
  if ("ResizeObserver" in window) {
    graphResizeObserver = new ResizeObserver(redraw);
    graphResizeObserver.observe(document.getElementById("wave-dag"));
    graphResizeObserver.observe(document.getElementById("dag"));
  }
}

function card(title, body) {
  const section = element("section");
  section.className = "detail-card";
  section.append(element("h3", title), body);
  return section;
}

function addStatusLine(parent, label, value) {
  const line = element("p");
  line.className = "status-line";
  line.append(element("strong", `${label}: `), makeBadge(asText(value), value));
  parent.append(line);
}

function renderActualLean(items) {
  const body = element("ul");
  if (!items?.length) {
    body.append(element("li", "No imported Lean declaration is recorded for this field yet."));
    return body;
  }
  for (const item of items) {
    const li = element("li");
    const path = item.source?.path || item.path || modulePath(item.module);
    const line = item.source?.line || item.line;
    if (path) li.append(sourceLink(item.declaration || item.name || "Lean source", path, line));
    else li.append(element("code", item.declaration || item.name || "Lean declaration"));
    const role = item.role ? ` · ${item.role}` : "";
    if (role) li.append(element("span", role));
    body.append(li);
  }
  return body;
}

function renderExamples(examples = []) {
  const body = element("div");
  if (!examples.length) {
    body.append(element("p", "No separate route examples are recorded."));
    return body;
  }
  for (const example of examples) {
    const section = element("article");
    section.className = "route-card";
    section.append(element("p", routeName(example, 0)));
    const status = element("p");
    status.append(element("strong", "Status: "), makeBadge(example.status || "unknown", example.status));
    section.append(status);
    if (example.scope) section.append(element("p", example.scope));
    const links = element("p");
    links.className = "artifact-links";
    const source = example.source?.path || example.source;
    if (source) links.append(sourceLink("Example source", source, example.source?.line || example.line));
    if (links.childElementCount) section.append(links);
    if (example.declarations?.length) {
      const declarations = element("ul");
      for (const declaration of example.declarations) {
        const item = element("li");
        const name = typeof declaration === "string" ? declaration : declaration.name || declaration.declaration;
        const path = typeof declaration === "object" ? declaration.path || modulePath(declaration.module) : null;
        const line = typeof declaration === "object" ? declaration.line : null;
        if (path) item.append(sourceLink(name, path, line));
        else item.append(element("code", name));
        declarations.append(item);
      }
      section.append(declarations);
    }
    body.append(section);
  }
  return body;
}

function routeName(route, index) {
  const kind = String(route.kind || route.id || `Route ${index + 1}`);
  const description = `${route.id || ""} ${kind} ${route.scope || ""}`;
  if (/rank[_ -]?zero/i.test(description)) return "Rank-zero regulator route";
  if (/positive[_ -]?rank/i.test(description)) return "Positive-rank regulator route";
  return kind.replaceAll("_", " ");
}

function addDeclarationRefs(list, label, references) {
  if (!Array.isArray(references) || !references.length) return;
  const item = element("li");
  item.append(element("strong", `${label}: `));
  const names = element("span");
  references.forEach((reference, index) => {
    if (index) names.append(document.createTextNode(" · "));
    if (reference && typeof reference === "object") {
      const path = reference.path || modulePath(reference.module);
      if (path) names.append(sourceLink(reference.name || reference.declaration || "Lean declaration", path, reference.line));
      else names.append(element("code", reference.name || reference.declaration || asText(reference)));
      if (reference.role) names.append(element("small", ` (${reference.role})`));
    } else names.append(element("code", asText(reference)));
  });
  item.append(names);
  list.append(item);
}

function renderRoutes(routes = []) {
  const body = element("div");
  if (!routes.length) {
    body.append(element("p", "No proof route is recorded yet."));
    return body;
  }
  routes.forEach((route, index) => {
    const section = element("article");
    section.className = "route-card";
    section.append(element("p", routeName(route, index)));
    if (route.scope) section.append(element("p", route.scope));
    if (route.producerDispatch) {
      const p = element("p");
      p.append(element("strong", "Producer dispatch: "), element("code", asText(route.producerDispatch)));
      section.append(p);
    }
    const list = element("ul");
    const addItems = (label, values) => {
      if (values === undefined || values === null || values === "" ||
          (Array.isArray(values) && !values.length)) return;
      const item = element("li");
      item.append(element("strong", `${label}: `), element("code", Array.isArray(values) ? values.join(" · ") : asText(values)));
      list.append(item);
    };
    addDeclarationRefs(list, "Prerequisites", route.prerequisites);
    addItems("JSON input", route.json);
    addDeclarationRefs(list, "Claim", route.claim);
    addItems("Check id", route.check_id);
    addDeclarationRefs(list, "Checker", route.check);
    addDeclarationRefs(list, "Verifier", route.verify);
    addDeclarationRefs(list, "Output", route.output);
    addDeclarationRefs(list, "Fact", route.fact);
    addItems("Assumptions", route.assumptions);
    addItems("Checker scope", route.checkerScopes);
    addItems("Report-only scope", route.reportOnlyScopes);
    addItems("Metadata scope", route.metadataScopes);
    if (list.childElementCount) section.append(list);
    if (route.nextStep) section.append(element("p", `Next: ${route.nextStep}`));
    body.append(section);
  });
  return body;
}

function renderObservation(title, value) {
  const body = element("div");
  if (value && typeof value === "object" && !Array.isArray(value)) {
    for (const [key, item] of Object.entries(value)) {
      const p = element("p");
      const label = key.replaceAll("_", " ");
      if (item && typeof item === "object") {
        const disclosure = element("details");
        const summary = element("summary", `${label}${Array.isArray(item) ? ` (${item.length})` : ""}`);
        const pre = element("pre");
        pre.textContent = asText(item);
        disclosure.append(summary, pre);
        body.append(disclosure);
        continue;
      }
      p.append(element("strong", `${label}: `), element("span", asText(item)));
      body.append(p);
    }
  } else body.append(element("p", asText(value)));
  return card(title, body);
}

function renderDetails(node) {
  const root = document.getElementById("detail-content");
  root.replaceChildren();
  const grid = element("div");
  grid.className = "detail-grid";

  if (node.node_type !== "field") {
    grid.append(renderObservation("Dependency node", node));
    if (node.roadmap?.path) {
      const roadmap = element("div");
      roadmap.append(element("p", node.roadmap.heading || node.label || node.id));
      roadmap.append(sourceLink("Open roadmap source", node.roadmap.path, node.roadmap.line));
      const wave = (graph.waves || []).find(item => item.id === node.id);
      if (wave) roadmap.append(element("p", `${wave.field_count ?? wave.field_ids?.length ?? 0} table-qualified fields in this package.`));
      grid.append(card("Work package", roadmap));
    }
    const sourcePath = node.source?.path || node.path || modulePath(node.module);
    if (sourcePath) {
      const source = element("div");
      source.append(sourceLink(node.declaration || node.label || "Source declaration", sourcePath, node.source?.line || node.line));
      if (node.role) source.append(element("p", node.role));
      grid.append(card("Lean source", source));
    }
    root.append(grid);
    return;
  }

  const state = element("div");
  addStatusLine(state, "Catalogue", statusLabel(node.status));
  grid.append(card("Catalogue status", state));

  const blocker = node.blocker || {};
  const missing = element("div");
  if (blocker.layer) addStatusLine(missing, "Blocked at", blocker.layer);
  if (blocker.code) addStatusLine(missing, "Reason", blocker.code);
  missing.append(element("p", blocker.detail || "No blocker detail supplied."));
  grid.append(card("Missing components", missing));

  grid.append(card("Current Lean declarations", renderActualLean(node.actualLean)));
  const routes = renderRoutes(node.routes);
  if (node.producerDispatch) {
    const dispatch = element("p");
    dispatch.append(element("strong", "Generator dispatch: "), element("code", statusLabel(node.producerDispatch.status)));
    if (node.producerDispatch.producer_sources?.length) {
      dispatch.append(element("span", ` · inputs ${node.producerDispatch.producer_sources.join(", ")}`));
    }
    routes.prepend(dispatch);
  }
  grid.append(card("Proof routes and generator", routes));
  if (node.examples?.length) grid.append(card("Separate route examples", renderExamples(node.examples)));
  grid.append(renderObservation("Native source", node.native));
  grid.append(renderObservation("Consumer evidence", node.consumer));
  grid.append(renderObservation("Publication artifact", node.publication));

  if (["regulator", "sha", "sha_an", "sha_primes"].includes(node.field)) {
    const regulator = element("div");
    const zero = element("p");
    zero.append(element("strong", "Rank zero: "), element("span", "the empty Mordell–Weil basis has regulator 1; the rank-zero route needs an exact algebraic rank-zero proof."));
    const positive = element("p");
    positive.append(element("strong", "Positive rank: "), element("span", "prove a Mordell–Weil basis and enclose the determinant of its canonical-height pairing. This is a separate route and is not covered by the rank-zero case."));
    regulator.append(zero, positive);
    grid.append(card("Regulator alternatives", regulator));
  }

  root.append(grid);
}

function renderMilestones(node) {
  const target = document.getElementById("milestones");
  target.replaceChildren();
  if (node.node_type !== "field") return;
  const stages = node.stages || {};
  const roadmapStage = stages.roadmap || {};
  const leanStage = stages.lean || {};
  const generatorStage = stages.generator || {};
  const entries = [
    {
      title: "Roadmap witness",
      key: "roadmap",
      stage: roadmapStage,
      status: roadmapStage.status || (node.roadmap?.path ? "specified" : "not_supplied"),
      description: roadmapStage.scope || node.roadmap?.heading || "Field specification status; native observation is shown below."
    },
    {
      title: "Lean witness",
      key: "lean",
      stage: leanStage,
      status: leanStage.status || (node.routes?.length ? "scoped" : "not_sampled"),
      description: leanStage.scope || "Compiled route scope; imported consumer evidence is shown below."
    },
    {
      title: "Generator",
      key: "generator",
      stage: generatorStage,
      status: generatorStage.status || node.producerDispatch?.status || "not_run",
      description: `${generatorStage.scope || node.producerDispatch?.status || "No producer route recorded"}${generatorStage.example_status || node.producer?.status ? ` · 112.a2 replay: ${statusLabel(generatorStage.example_status || node.producer?.status)}` : ""}`
    }
  ];
  for (const milestone of entries) {
    const section = element("section");
    section.className = "milestone-card";
    section.append(element("h3", milestone.title));
    const statusLine = element("p");
    statusLine.append(element("strong", "Status: "), makeBadge(statusLabel(milestone.status), milestone.status));
    section.append(statusLine, element("p", milestone.description));
    if (milestone.key === "lean") {
      if (milestone.stage.accepts_external_evidence) {
        const evidence = milestone.stage.external_evidence || [];
        section.append(element("p", `Accepts supplied evidence${evidence.length ? `: ${evidence.join(", ")}` : ""}.`));
      }
      for (const alternative of milestone.stage.report_only_alternatives || []) {
        section.append(element("p", `Report only: ${alternative}`));
      }
    }
    const artifactLinks = element("p");
    artifactLinks.className = "artifact-links";
    if (milestone.key === "roadmap") {
      artifactLinks.append(sourceLink("Native capture", "tests/fixtures/lmfdb/112.a2-native.json"));
      artifactLinks.append(sourceLink("Provenance", "tests/fixtures/lmfdb/112.a2-native.provenance.json"));
      const source = milestone.stage.source || node.roadmap;
      if (source?.path) artifactLinks.append(sourceLink("Field contract", source.path, source.line));
    } else if (milestone.key === "lean") {
      if (milestone.stage.source?.path) {
        artifactLinks.append(sourceLink("Compiled route", milestone.stage.source.path, milestone.stage.source.line));
      } else if (node.catalogueLink?.path) {
        artifactLinks.append(sourceLink("Catalogue route", node.catalogueLink.path, node.catalogueLink.line));
      }
      const witnessFields = [...(node.actualLean || [])].sort((left, right) => Number(right.role === "claim") - Number(left.role === "claim"));
      for (const proof of [...witnessFields, ...(node.consumer?.evidence || [])]) {
        const path = proof.source?.path || proof.source || proof.path || modulePath(proof.module);
        if (path) {
          artifactLinks.append(sourceLink(proof.declaration || proof.theorem || "Witness field", path, proof.source?.line || proof.proof_line || proof.line));
          break;
        }
      }
    } else if (milestone.key === "generator") {
      const source = milestone.stage.source;
      artifactLinks.append(source?.path
        ? sourceLink("Generator route", source.path, source.line)
        : sourceLink("Producer source", "scripts/produce_ec_witness.py"));
    }
    if (artifactLinks.childElementCount) section.append(artifactLinks);
    target.append(section);
  }
}

function selectNode(id, updateHash = false) {
  const node = nodeById.get(id);
  if (!node) return;
  selectedId = id;
  if (node.node_type === "field" || node.node_type === "milestone") {
    selectedWave = node.wave || "";
    renderWaveOverview();
  }
  if (updateHash) history.pushState(null, "", `#${encodeURIComponent(id)}`);
  document.getElementById("share-link").href = `#${encodeURIComponent(id)}`;
  document.getElementById("share-link").textContent = `Link to ${node.label || id}`;
  document.getElementById("graph-caption").textContent = `${node.label || id} · arrows show direct prerequisite-to-dependent edges.`;

  const dependencies = (incoming.get(id) || []).map(edge => ({
    id: edge.from,
    reason: edge.reason,
    kind: edge.kind
  })).filter(edge => nodeById.has(edge.id));
  const dependents = (outgoing.get(id) || []).map(edge => ({
    id: edge.to,
    reason: edge.reason,
    kind: edge.kind
  })).filter(edge => nodeById.has(edge.id));
  edgeItems(document.getElementById("prerequisites"), dependencies, "No direct field prerequisites.");
  edgeItems(document.getElementById("dependents"), dependents, "No direct dependent claims.");
  document.getElementById("selected-node").replaceChildren(nodeButton(id, true));
  document.getElementById("no-edges").hidden = Boolean(dependencies.length || dependents.length);
  document.getElementById("detail-intro").textContent = node.node_type === "field"
    ? `${node.table}.${node.field} · ${node.label || node.field}`
    : node.node_type === "milestone"
      ? `${node.wave} · ${node.label}`
      : `${node.label || node.id} · ${node.node_type || "dependency"}`;
  renderMilestones(node);
  renderDetails(node);
  renderFieldList();
  requestAnimationFrame(() => redrawGraph());
}

function handleHash() {
  const raw = decodeURIComponent(location.hash.slice(1));
  if (nodeById.has(raw)) selectNode(raw, false);
}

function renderInitialControls() {
  const fieldNodes = graph.nodes.filter(node => node.node_type === "field");
  const tables = [...new Set(fieldNodes.map(node => node.table))].sort();
  for (const table of tables) {
    const option = element("option", table);
    option.value = table;
    tableFilter.append(option);
  }
  for (const control of [search, tableFilter, statusFilter, blockerFilter]) {
    control.addEventListener(control === search || control === blockerFilter ? "input" : "change", renderFieldList);
  }
  document.getElementById("clear").addEventListener("click", () => {
    search.value = "";
    tableFilter.value = "";
    statusFilter.value = "";
    blockerFilter.checked = false;
    selectedWave = "";
    renderWaveOverview();
    renderFieldList();
    search.focus();
  });
  document.getElementById("all-waves").addEventListener("click", () => {
    selectedWave = "";
    renderWaveOverview();
    renderFieldList();
  });
  window.addEventListener("hashchange", handleHash);
  window.addEventListener("popstate", handleHash);
  document.getElementById("filters").disabled = false;
  document.getElementById("workspace").hidden = false;
  document.getElementById("wave-overview").hidden = false;
  renderWaveOverview();
  renderFieldList();
  handleHash();
  if (!selectedId && fieldNodes.length) selectNode(fieldNodes[0].id);
}

async function load() {
  const response = await fetch(graphPath);
  if (!response.ok) throw new Error("Field roadmap data unavailable");
  graph = await response.json();
  if (graph.schema !== "lcalc.lmfdb-field-dependency-roadmap.v1" ||
      !Array.isArray(graph.nodes) || !Array.isArray(graph.edges)) {
    throw new Error("Unknown field roadmap format");
  }
  nodeById = new Map(graph.nodes.map(node => [node.id, node]));
  incoming = new Map(graph.nodes.map(node => [node.id, []]));
  outgoing = new Map(graph.nodes.map(node => [node.id, []]));
  for (const edge of graph.edges) {
    if (!nodeById.has(edge.from) || !nodeById.has(edge.to)) continue;
    outgoing.get(edge.from).push(edge);
    incoming.get(edge.to).push(edge);
  }
  graph.nodes.sort((a, b) => a.id.localeCompare(b.id));
  redrawGraph = redrawAllGraphs;
  installGraphResizeObserver();
  renderInitialControls();
  const fieldCount = graph.nodes.filter(node => node.node_type === "field").length;
  const packageCount = graph.waves?.length || graph.nodes.filter(node => node.node_type === "milestone").length;
  loadStatus.textContent = `${fieldCount} table-qualified fields, ${packageCount} work packages, and ${graph.edges.length} directed links loaded.`;
  loadStatus.dataset.state = "ready";
}

load().catch(() => {
  loadStatus.textContent = "Unable to load the certificate dependency roadmap.";
  loadStatus.dataset.state = "warning";
});
