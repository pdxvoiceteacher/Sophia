import { renderGlossary } from "./glossary.js";
import { loadZipFile, loadFolderFiles } from "./zip_loader.js";
import {
  renderSummary,
  renderTopRisks,
  renderActions,
  renderArtifacts,
  renderClaims,
  renderContradictions,
  renderEvents,
  renderGovernanceOverview,
  renderLegitimacyStrip,
  renderDueProcess,
  renderElection,
  renderDecisionProof,
  renderLedgerAnchor,
  renderWarrant,
  renderExecution,
  renderExecutionDiffs,
} from "./ui.js";

const state = {
  runs: [],
  files: {},
  selectedRun: null,
  normalized: null,
  density: "medium",
  plainMode: true,
  evidenceMode: false,
};

const elements = {
  runPicker: document.getElementById("run-picker"),
  zipInput: document.getElementById("zip-input"),
  folderInput: document.getElementById("folder-input"),
  dropZone: document.getElementById("drop-zone"),
  summary: document.getElementById("summary"),
  topRisks: document.getElementById("top-risks"),
  actions: document.getElementById("recommended-actions"),
  artifacts: document.getElementById("artifacts"),
  claims: document.getElementById("claims"),
  contradictions: document.getElementById("contradictions"),
  events: document.getElementById("events"),
  governanceOverview: document.getElementById("governance-overview"),
  legitimacyStrip: document.getElementById("legitimacy-strip"),
  continuityPanel: document.getElementById("continuity-panel"),
  shutdownPanel: document.getElementById("shutdown-panel"),
  electionSummary: document.getElementById("election-summary"),
  decisionProof: document.getElementById("decision-proof"),
  ledgerAnchor: document.getElementById("ledger-anchor"),
  warrant: document.getElementById("warrant"),
  executionReceipt: document.getElementById("execution-receipt"),
  executionDiffs: document.getElementById("execution-diffs"),
  jsonViewer: document.getElementById("json-viewer"),
  tabs: document.querySelectorAll(".tab"),
  views: document.querySelectorAll(".view"),
  density: document.getElementById("density"),
  fontSize: document.getElementById("font-size"),
  lineSpacing: document.getElementById("line-spacing"),
  oneAtATime: document.getElementById("one-at-a-time"),
  togglePlain: document.getElementById("toggle-plain"),
  toggleEvidence: document.getElementById("toggle-evidence"),
  copyCommand: document.getElementById("copy-command"),
  copyPr: document.getElementById("copy-pr"),
  copyBug: document.getElementById("copy-bug"),
  glossary: document.getElementById("glossary"),
};

renderGlossary(elements.glossary);

function setRunOptions() {
  elements.runPicker.innerHTML = "";
  state.runs.forEach((run) => {
    const option = document.createElement("option");
    option.value = run.name;
    option.textContent = run.name;
    elements.runPicker.appendChild(option);
  });
}

function decodeJson(path) {
  const data = state.files[path];
  if (!data) return null;
  const text = new TextDecoder("utf-8").decode(data);
  try {
    return JSON.parse(text);
  } catch (error) {
    return null;
  }
}

function findFilePath(run, fileName) {
  if (!run) return null;
  const root = run.rootPath === "(root)" ? "" : `${run.rootPath}/`;
  const match = run.files.find((path) => path.endsWith(`${root}${fileName}`));
  return match || run.files.find((path) => path.endsWith(fileName));
}

function buildNormalized(run) {
  const telemetryPath = findFilePath(run, "telemetry.json");
  const auditPath = findFilePath(run, "sophia_audit.json");
  const planPath = findFilePath(run, "sophia_plan.json");
  const bundlePath = findFilePath(run, "audit_bundle.json");
  const electionPath = findFilePath(run, "election.json");
  const tallyPath = findFilePath(run, "tally.json");
  const decisionPath = findFilePath(run, "decision.json");
  const warrantPath = findFilePath(run, "warrant.json");
  const continuityClaimPath = findFilePath(run, "continuity_claim.json");
  const continuityWarrantPath = findFilePath(run, "continuity_warrant.json");
  const shutdownWarrantPath = findFilePath(run, "shutdown_warrant.json");
  const receiptPath = findFilePath(run, "execution_receipt.json");
  const policyResolutionPath = findFilePath(run, "policy_resolution.json");

  const telemetry = telemetryPath ? decodeJson(telemetryPath) : null;
  const sophiaAudit = auditPath ? decodeJson(auditPath) : null;
  const sophiaPlan = planPath ? decodeJson(planPath) : null;
  const auditBundle = bundlePath ? decodeJson(bundlePath) : null;
  const election = electionPath ? decodeJson(electionPath) : null;
  const tally = tallyPath ? decodeJson(tallyPath) : null;
  const decision = decisionPath ? decodeJson(decisionPath) : null;
  const warrant = warrantPath ? decodeJson(warrantPath) : null;
  const continuityClaim = continuityClaimPath ? decodeJson(continuityClaimPath) : null;
  const continuityWarrant = continuityWarrantPath ? decodeJson(continuityWarrantPath) : null;
  const shutdownWarrant = shutdownWarrantPath ? decodeJson(shutdownWarrantPath) : null;
  const executionReceipt = receiptPath ? decodeJson(receiptPath) : null;
  const policyResolution = policyResolutionPath ? decodeJson(policyResolutionPath) : null;

  const filesIndex = run.files.map((path) => ({
    path,
    size: run.sizes[path] || state.files[path]?.byteLength || 0,
  }));

  const derived = {
    decision: sophiaAudit?.decision || sophiaPlan?.decision || "unknown",
    riskScore: sophiaPlan?.risk_score || sophiaAudit?.metrics_snapshot?.risk_score || null,
    topRisks: sophiaPlan?.top_risks || [],
    recommendedActions: sophiaPlan?.recommended_actions || [],
    metrics: {
      Psi: telemetry?.metrics?.Psi ?? telemetry?.metrics?.psi ?? null,
      DeltaS: telemetry?.metrics?.DeltaS ?? telemetry?.metrics?.delta_s ?? null,
      Lambda: telemetry?.metrics?.Lambda ?? telemetry?.metrics?.lambda ?? null,
      Es: telemetry?.metrics?.Es ?? telemetry?.metrics?.es ?? null,
    },
    mode: sophiaAudit?.trend_summary?.mode_guardrails ? "ci" : sophiaPlan?.mode || "ci",
    contradictionsSummary: sophiaAudit?.contradiction_clusters || [],
    eventsSummary: deriveEventSummary(run),
  };

  return {
    runDirName: run.name,
    telemetry,
    sophiaAudit,
    sophiaPlan,
    auditBundle,
    election,
    tally,
    decision,
    warrant,
    continuityClaim,
    continuityWarrant,
    shutdownWarrant,
    executionReceipt,
    policyResolution,
    filesIndex,
    derived,
  };
}

function deriveEventSummary(run) {
  const telPath = findFilePath(run, "tel.json");
  const telEventsPath = findFilePath(run, "tel_events.jsonl");
  const uccPath = findFilePath(run, "ucc_tel_events.jsonl");

  const summary = {};
  if (telPath) {
    const content = decodeJson(telPath);
    summary.telCount = Array.isArray(content) ? content.length : 0;
  }
  if (telEventsPath) {
    const text = new TextDecoder("utf-8").decode(state.files[telEventsPath] || new Uint8Array());
    summary.telEventsCount = text.trim() ? text.trim().split("\n").length : 0;
  }
  if (uccPath) {
    const text = new TextDecoder("utf-8").decode(state.files[uccPath] || new Uint8Array());
    summary.uccEventsCount = text.trim() ? text.trim().split("\n").length : 0;
  }
  return Object.keys(summary).length ? summary : null;
}

function render() {
  renderSummary(elements.summary, state.normalized);
  renderTopRisks(elements.topRisks, state.normalized);
  renderActions(elements.actions, state.normalized);
  renderArtifacts(elements.artifacts, state.normalized);
  renderClaims(elements.claims, state.normalized);
  renderContradictions(elements.contradictions, state.normalized);
  renderEvents(elements.events, state.normalized);
  renderGovernanceOverview(elements.governanceOverview, state.normalized);
  renderLegitimacyStrip(elements.legitimacyStrip, state.normalized);
  renderDueProcess(elements.continuityPanel, elements.shutdownPanel, state.normalized);
  renderElection(elements.electionSummary, state.normalized);
  renderDecisionProof(elements.decisionProof, state.normalized);
  renderLedgerAnchor(elements.ledgerAnchor, state.normalized);
  renderWarrant(elements.warrant, state.normalized);
  renderExecution(elements.executionReceipt, state.normalized);
  renderExecutionDiffs(elements.executionDiffs, state.normalized);
  updateGovernanceVisibility();
  if (state.normalized) {
    elements.jsonViewer.textContent = JSON.stringify(state.normalized.sophiaAudit || {}, null, 2);
  }
}

function updateGovernanceVisibility() {
  if (!state.normalized) return;
  const hasGovernance =
    state.normalized.election ||
    state.normalized.tally ||
    state.normalized.decision ||
    state.normalized.warrant ||
    state.normalized.continuityClaim ||
    state.normalized.continuityWarrant ||
    state.normalized.shutdownWarrant ||
    state.normalized.policyResolution ||
    state.normalized.executionReceipt;
  const governanceTabs = ["election", "warrant", "execution"];
  governanceTabs.forEach((view) => {
    const tab = document.querySelector(`.tab[data-view="${view}"]`);
    const panel = document.getElementById(`view-${view}`);
    if (tab) tab.classList.toggle("hidden", !hasGovernance);
    if (panel) panel.classList.toggle("hidden", !hasGovernance);
  });
  if (elements.governanceOverview) {
    elements.governanceOverview.closest(".card")?.classList.toggle("hidden", !hasGovernance);
  }
}

async function loadRunFromZip(file) {
  const result = await loadZipFile(file);
  state.runs = result.runs;
  state.files = result.files;
  setRunOptions();
  selectRun(state.runs[0]?.name);
}

async function loadRunFromFolder(files) {
  const result = await loadFolderFiles(files);
  state.runs = result.runs;
  state.files = result.files;
  setRunOptions();
  selectRun(state.runs[0]?.name);
}

function selectRun(name) {
  const run = state.runs.find((item) => item.name === name);
  if (!run) return;
  state.selectedRun = run;
  state.normalized = buildNormalized(run);
  render();
}

function setDensity(value) {
  document.body.classList.remove("density-low", "density-medium", "density-high");
  document.body.classList.add(`density-${value}`);
}

function togglePlainMode() {
  state.plainMode = !state.plainMode;
  document.body.classList.toggle("plain", state.plainMode);
}

function toggleEvidenceMode() {
  state.evidenceMode = !state.evidenceMode;
  document.body.classList.toggle("evidence", state.evidenceMode);
}

function copyText(text) {
  navigator.clipboard.writeText(text);
}

function getNextCommand() {
  if (!state.normalized) return "";
  return `python tools/telemetry/sophia_audit.py --run-dir out/${state.normalized.runDirName} --repo-root .`;
}

function getPrSnippet() {
  if (!state.normalized) return "";
  const risks = state.normalized.derived.topRisks.map((risk) => `- ${risk.type}: ${risk.summary}`).join("\n");
  return `## Sophia Audit Summary\nDecision: ${state.normalized.derived.decision}\nRisk score: ${state.normalized.derived.riskScore}\n\n### Top Risks\n${risks}`;
}

function getBugTemplate() {
  if (!state.normalized) return "";
  return `## Bug report\nRun: ${state.normalized.runDirName}\nDecision: ${state.normalized.derived.decision}\nRisk score: ${state.normalized.derived.riskScore}\n\n### Findings\n${JSON.stringify(state.normalized.sophiaAudit?.findings || [], null, 2)}`;
}

function attachListeners() {
  elements.runPicker.addEventListener("change", (event) => selectRun(event.target.value));
  elements.zipInput.addEventListener("change", (event) => loadRunFromZip(event.target.files[0]));
  elements.folderInput.addEventListener("change", (event) => loadRunFromFolder(event.target.files));

  elements.dropZone.addEventListener("dragover", (event) => {
    event.preventDefault();
    elements.dropZone.classList.add("active");
  });
  elements.dropZone.addEventListener("dragleave", () => elements.dropZone.classList.remove("active"));
  elements.dropZone.addEventListener("drop", (event) => {
    event.preventDefault();
    elements.dropZone.classList.remove("active");
    const file = event.dataTransfer.files[0];
    if (file && file.name.endsWith(".zip")) {
      loadRunFromZip(file);
    }
  });

  elements.tabs.forEach((tab) => {
    tab.addEventListener("click", () => {
      elements.tabs.forEach((button) => button.classList.remove("active"));
      elements.views.forEach((view) => view.classList.remove("active"));
      tab.classList.add("active");
      document.getElementById(`view-${tab.dataset.view}`).classList.add("active");
    });
  });

  elements.density.addEventListener("change", (event) => {
    setDensity(event.target.value);
  });

  elements.fontSize.addEventListener("input", (event) => {
    document.documentElement.style.setProperty("--font-size", `${event.target.value}px`);
  });

  elements.lineSpacing.addEventListener("input", (event) => {
    document.documentElement.style.setProperty("--line-height", event.target.value);
  });

  elements.oneAtATime.addEventListener("change", (event) => {
    document.body.classList.toggle("one-at-a-time", event.target.checked);
  });

  elements.togglePlain.addEventListener("click", togglePlainMode);
  elements.toggleEvidence.addEventListener("click", toggleEvidenceMode);

  document.querySelectorAll("[data-json]").forEach((button) => {
    button.addEventListener("click", () => {
      if (!state.selectedRun) return;
      const path = findFilePath(state.selectedRun, button.dataset.json);
      const data = path ? decodeJson(path) : null;
      elements.jsonViewer.textContent = data ? JSON.stringify(data, null, 2) : "Missing file.";
    });
  });

  elements.copyCommand.addEventListener("click", () => copyText(getNextCommand()));
  elements.copyPr.addEventListener("click", () => copyText(getPrSnippet()));
  elements.copyBug.addEventListener("click", () => copyText(getBugTemplate()));
}

setDensity(state.density);
document.body.classList.toggle("plain", state.plainMode);
attachListeners();
render();
