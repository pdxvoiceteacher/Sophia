import { invoke } from "@tauri-apps/api/tauri";

const elements = {
  centralStandards: document.getElementById("central-standards"),
  localLlm: document.getElementById("local-llm"),
  gatewayPort: document.getElementById("gateway-port"),
  saveButton: document.getElementById("save-config"),
  saveStatus: document.getElementById("save-status"),
  gatewayStatus: document.getElementById("gateway-status"),
  uccStatus: document.getElementById("ucc-status"),
  checkCentralSync: document.getElementById("check-central-sync"),
  viewerFrame: document.getElementById("viewer-frame"),
  connectorType: document.getElementById("connector-type"),
  connectorEndpoint: document.getElementById("connector-endpoint"),
  connectorModel: document.getElementById("connector-model"),
  testConnector: document.getElementById("test-connector"),
  connectorStatus: document.getElementById("connector-status"),
  epochBaselineScenario: document.getElementById("epoch-baseline-scenario"),
  epochExperimentalScenario: document.getElementById("epoch-experimental-scenario"),
  runEpochTest: document.getElementById("run-epoch-test"),
  epochStatus: document.getElementById("epoch-status"),
  epochSummary: document.getElementById("epoch-summary"),
  epochRunFolder: document.getElementById("epoch-run-folder"),
  reviewCentralUrl: document.getElementById("review-central-url"),
  reviewSubmitterId: document.getElementById("review-submitter-id"),
  submitCrossReview: document.getElementById("submit-cross-review"),
  fetchAttestations: document.getElementById("fetch-attestations"),
  reviewStatus: document.getElementById("review-status"),
  reviewSubmissionId: document.getElementById("review-submission-id"),
  reviewAttestationPath: document.getElementById("review-attestation-path"),
};

const state = {
  port: null,
  config: null,
  scenarios: [],
  lastEpochResult: null,
  lastSubmissionId: null,
};

function setChipStatus(element, label, status, ok = false) {
  element.textContent = `${label}: ${status}`;
  element.classList.toggle("ok", ok);
  element.classList.toggle("down", !ok);
}

function getConnectorPayload() {
  return {
    connector_type: elements.connectorType.value,
    connector_endpoint: elements.connectorEndpoint.value.trim() || null,
    connector_model: elements.connectorModel.value.trim() || null,
  };
}

function endpointHost(endpoint) {
  if (!endpoint) return null;
  try {
    return new URL(endpoint).hostname;
  } catch {
    return null;
  }
}

function populateScenarioSelects(scenarios) {
  [elements.epochBaselineScenario, elements.epochExperimentalScenario].forEach((select) => {
    select.innerHTML = "";
    scenarios.forEach((item) => {
      const opt = document.createElement("option");
      opt.value = item;
      opt.textContent = item;
      select.appendChild(opt);
    });
  });
  const baseline = scenarios.find((s) => s.includes("baseline"));
  const experimental = scenarios.find((s) => s.includes("experimental"));
  if (baseline) elements.epochBaselineScenario.value = baseline;
  if (experimental) elements.epochExperimentalScenario.value = experimental;
}

async function loadState() {
  const result = await invoke("get_terminal_state");
  state.port = result.port;
  state.config = result.config;
  elements.gatewayPort.value = String(state.port);
  elements.centralStandards.value = state.config.central_standards_url || "";
  elements.localLlm.value = state.config.local_llm_url || "";
  elements.connectorType.value = state.config.connector_type || "LocalLLMConnector";
  elements.connectorEndpoint.value = state.config.connector_endpoint || "";
  elements.connectorModel.value = state.config.connector_model || "";
  elements.viewerFrame.src = `http://127.0.0.1:${state.port}/sophia/viewer`;

  state.scenarios = await invoke("list_epoch_scenarios");
  populateScenarioSelects(state.scenarios);
}

async function saveConfig() {
  const connector = getConnectorPayload();
  const enabledMarketFlags = state.config?.enabled_market_flags || [];
  const payload = {
    central_standards_url: elements.centralStandards.value.trim(),
    local_llm_url: elements.localLlm.value.trim() || null,
    ...connector,
    enabled_market_flags: enabledMarketFlags,
  };

  try {
    await invoke("validate_enabled_market_flags", { flags: enabledMarketFlags });
    await invoke("save_terminal_config", { config: payload });
    state.config = payload;
    elements.saveStatus.textContent = "Saved";
  } catch (error) {
    elements.saveStatus.textContent = `Save blocked: ${String(error)}`;
  }

  setTimeout(() => {
    elements.saveStatus.textContent = "";
  }, 2500);
}

async function logConnector(status) {
  const connector = getConnectorPayload();
  const envelope = {
    connector_type: connector.connector_type,
    endpoint_host: endpointHost(connector.connector_endpoint),
    model: connector.connector_model,
    status,
    timestamp_utc: new Date().toISOString(),
  };
  await invoke("log_connector_event", { envelope });
}

async function testConnectorConnection() {
  const endpoint = elements.connectorEndpoint.value.trim();
  if (!endpoint) {
    elements.connectorStatus.textContent = "Connector endpoint required.";
    return;
  }
  try {
    const result = await invoke("test_connector_endpoint", { endpoint });
    const status = result.ok ? "ok" : "failed";
    elements.connectorStatus.textContent = `${result.detail} (${result.latency_ms}ms)`;
    await logConnector(status);
  } catch (error) {
    elements.connectorStatus.textContent = `Connection failed: ${String(error)}`;
    await logConnector("failed");
  }
}

async function checkCentralSyncStatus() {
  const centralUrl = elements.centralStandards.value.trim();
  if (!centralUrl) {
    setChipStatus(elements.uccStatus, "UCC Sync", "down", false);
    return;
  }
  try {
    const sync = await invoke("check_central_sync", { centralUrl });
    const ok = sync.status === "ok" || sync.status === "stale";
    setChipStatus(elements.uccStatus, "UCC Sync", sync.status, ok);
  } catch {
    setChipStatus(elements.uccStatus, "UCC Sync", "down", false);
  }
}

async function runEpochTest() {
  const baselineScenario = elements.epochBaselineScenario.value;
  const experimentalScenario = elements.epochExperimentalScenario.value;
  if (!baselineScenario || !experimentalScenario) {
    elements.epochStatus.textContent = "Select baseline and experimental scenarios.";
    return;
  }

  elements.epochStatus.textContent = "Running scenario-based epoch test...";
  try {
    const result = await invoke("run_epoch_test", {
      baselineScenario,
      experimentalScenario,
      seed: 7,
    });
    state.lastEpochResult = result;
    elements.epochStatus.textContent = "Complete";
    elements.epochSummary.textContent = `TEL hash eq: ${result.tel_hash_equal} • branch divergence: ${result.branch_divergence} • entropy spikes: ${result.entropy_spikes} • ΔPsi max: ${result.delta_psi_max} • Es drift: ${result.es_drift}`;
    elements.epochRunFolder.textContent = result.run_folder || "n/a";
    await invoke("log_epoch_event", { envelope: result });
  } catch (error) {
    elements.epochStatus.textContent = `Failed: ${String(error)}`;
  }
}

async function submitCrossReview() {
  if (!state.lastEpochResult?.run_folder) {
    elements.reviewStatus.textContent = "Run an epoch test first.";
    return;
  }
  elements.reviewStatus.textContent = "Creating submission bundle...";
  try {
    const result = await invoke("create_cross_review_submission", {
      runFolder: state.lastEpochResult.run_folder,
      submitterId: elements.reviewSubmitterId.value.trim() || null,
      centralUrl: elements.reviewCentralUrl.value.trim() || null,
    });
    state.lastSubmissionId = result.submission_id;
    elements.reviewStatus.textContent = result.detail;
    elements.reviewSubmissionId.textContent = result.submission_id;
    elements.reviewAttestationPath.textContent = result.bundle_path;
  } catch (error) {
    elements.reviewStatus.textContent = `Submit failed: ${String(error)}`;
  }
}

async function fetchAttestations() {
  const submissionId = state.lastSubmissionId || elements.reviewSubmissionId.textContent;
  if (!submissionId || submissionId === "n/a") {
    elements.reviewStatus.textContent = "No submission ID available.";
    return;
  }
  elements.reviewStatus.textContent = "Fetching attestations...";
  try {
    const result = await invoke("fetch_attestations", {
      submissionId,
      centralUrl: elements.reviewCentralUrl.value.trim() || null,
    });
    elements.reviewStatus.textContent = result.detail;
    elements.reviewAttestationPath.textContent = result.attestation_path;
  } catch (error) {
    elements.reviewStatus.textContent = `Fetch failed: ${String(error)}`;
  }
}

async function pollHealth() {
  if (!state.port) return;
  try {
    const base = `http://127.0.0.1:${state.port}`;
    const [health, wellKnown] = await Promise.all([fetch(`${base}/healthz`), fetch(`${base}/.well-known/sophia.json`)]);
    const gatewayOk = health.ok && wellKnown.ok;
    setChipStatus(elements.gatewayStatus, "Gateway", gatewayOk ? "OK" : "Down", gatewayOk);
  } catch {
    setChipStatus(elements.gatewayStatus, "Gateway", "Down", false);
  }
}

function attachEvents() {
  elements.saveButton.addEventListener("click", saveConfig);
  elements.testConnector.addEventListener("click", testConnectorConnection);
  elements.checkCentralSync.addEventListener("click", checkCentralSyncStatus);
  elements.runEpochTest.addEventListener("click", runEpochTest);
  elements.submitCrossReview.addEventListener("click", submitCrossReview);
  elements.fetchAttestations.addEventListener("click", fetchAttestations);
}

async function start() {
  attachEvents();
  await loadState();
  await pollHealth();
  await checkCentralSyncStatus();
  setInterval(pollHealth, 5000);
}

start();
