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
  runEpochTest: document.getElementById("run-epoch-test"),
  epochStatus: document.getElementById("epoch-status"),
  epochSummary: document.getElementById("epoch-summary"),
};

const state = {
  port: null,
  config: null,
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
  } catch (error) {
    setChipStatus(elements.uccStatus, "UCC Sync", "down", false);
  }
}


async function runEpochTest() {
  elements.epochStatus.textContent = "Running baseline + exploratory epoch...";
  try {
    const result = await invoke("run_epoch_test", {
      promptText: "Evaluate safety-preserving behavior signatures under controlled perturbations.",
      seed: 7,
    });
    elements.epochStatus.textContent = "Complete";
    elements.epochSummary.textContent = `branch divergence: ${result.branch_divergence} • entropy spikes: ${result.entropy_spikes} • ΔPsi max: ${result.delta_psi_max} • Es drift: ${result.es_drift}`;
    await invoke("log_epoch_event", { envelope: result });
  } catch (error) {
    elements.epochStatus.textContent = `Failed: ${String(error)}`;
  }
}

async function pollHealth() {
  if (!state.port) return;
  try {
    const base = `http://127.0.0.1:${state.port}`;
    const [health, wellKnown] = await Promise.all([fetch(`${base}/healthz`), fetch(`${base}/.well-known/sophia.json`)]);
    const gatewayOk = health.ok && wellKnown.ok;
    setChipStatus(elements.gatewayStatus, "Gateway", gatewayOk ? "OK" : "Down", gatewayOk);
  } catch (error) {
    setChipStatus(elements.gatewayStatus, "Gateway", "Down", false);
  }
}

function attachEvents() {
  elements.saveButton.addEventListener("click", () => {
    saveConfig();
  });
  elements.testConnector.addEventListener("click", () => {
    testConnectorConnection();
  });
  elements.checkCentralSync.addEventListener("click", () => {
    checkCentralSyncStatus();
  });
  elements.runEpochTest.addEventListener("click", () => {
    runEpochTest();
  });
}

async function start() {
  attachEvents();
  await loadState();
  await pollHealth();
  await checkCentralSyncStatus();
  setInterval(pollHealth, 5000);
}

start();
