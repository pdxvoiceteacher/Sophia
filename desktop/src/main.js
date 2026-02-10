import { invoke } from "@tauri-apps/api/tauri";

const elements = {
  centralStandards: document.getElementById("central-standards"),
  localLlm: document.getElementById("local-llm"),
  gatewayPort: document.getElementById("gateway-port"),
  saveButton: document.getElementById("save-config"),
  saveStatus: document.getElementById("save-status"),
  gatewayStatus: document.getElementById("gateway-status"),
<<<<<<< HEAD
  uccStatus: document.getElementById("ucc-status"),
  viewerFrame: document.getElementById("viewer-frame"),
  connectorType: document.getElementById("connector-type"),
  connectorEndpoint: document.getElementById("connector-endpoint"),
  connectorModel: document.getElementById("connector-model"),
  testConnector: document.getElementById("test-connector"),
  connectorStatus: document.getElementById("connector-status"),
=======
  viewerFrame: document.getElementById("viewer-frame"),
>>>>>>> origin/main
};

const state = {
  port: null,
  config: null,
};

<<<<<<< HEAD
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
=======
function setStatus(ok) {
  elements.gatewayStatus.textContent = ok ? "Gateway: OK" : "Gateway: Down";
  elements.gatewayStatus.classList.toggle("ok", ok);
  elements.gatewayStatus.classList.toggle("down", !ok);
>>>>>>> origin/main
}

async function loadState() {
  const result = await invoke("get_terminal_state");
  state.port = result.port;
  state.config = result.config;
  elements.gatewayPort.value = String(state.port);
  elements.centralStandards.value = state.config.central_standards_url || "";
  elements.localLlm.value = state.config.local_llm_url || "";
<<<<<<< HEAD
  elements.connectorType.value = state.config.connector_type || "LocalLLMConnector";
  elements.connectorEndpoint.value = state.config.connector_endpoint || "";
  elements.connectorModel.value = state.config.connector_model || "";
=======
>>>>>>> origin/main
  elements.viewerFrame.src = `http://127.0.0.1:${state.port}/sophia/viewer`;
}

async function saveConfig() {
<<<<<<< HEAD
  const connector = getConnectorPayload();
  const payload = {
    central_standards_url: elements.centralStandards.value.trim(),
    local_llm_url: elements.localLlm.value.trim() || null,
    ...connector,
=======
  const payload = {
    central_standards_url: elements.centralStandards.value.trim(),
    local_llm_url: elements.localLlm.value.trim() || null,
>>>>>>> origin/main
  };
  await invoke("save_terminal_config", { config: payload });
  elements.saveStatus.textContent = "Saved";
  setTimeout(() => {
    elements.saveStatus.textContent = "";
  }, 1500);
}

<<<<<<< HEAD
async function logConnector(status) {
  const connector = getConnectorPayload();
  const envelope = {
    connector_type: connector.connector_type,
    endpoint: connector.connector_endpoint,
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
    const response = await fetch(endpoint, { method: "GET", mode: "cors" });
    const status = response.ok ? "ok" : `http_${response.status}`;
    elements.connectorStatus.textContent = `Connection ${status}`;
    await logConnector(status);
  } catch (error) {
    elements.connectorStatus.textContent = "Connection failed";
    await logConnector("failed");
  }
}

=======
>>>>>>> origin/main
async function pollHealth() {
  if (!state.port) return;
  try {
    const base = `http://127.0.0.1:${state.port}`;
<<<<<<< HEAD
    const [health, wellKnown, ucc] = await Promise.all([
      fetch(`${base}/healthz`),
      fetch(`${base}/.well-known/sophia.json`),
      fetch(`${base}/ucc/index`),
    ]);
    const gatewayOk = health.ok && wellKnown.ok;
    setChipStatus(elements.gatewayStatus, "Gateway", gatewayOk ? "OK" : "Down", gatewayOk);
    let uccText = "failed";
    if (ucc.ok) {
      const payload = await ucc.json();
      uccText = payload.status || "ok";
    }
    const uccOk = ucc.ok && (uccText === "ok" || uccText === "stale");
    setChipStatus(elements.uccStatus, "UCC Sync", uccText, uccOk);
  } catch (error) {
    setChipStatus(elements.gatewayStatus, "Gateway", "Down", false);
    setChipStatus(elements.uccStatus, "UCC Sync", "failed", false);
=======
    const [health, wellKnown] = await Promise.all([
      fetch(`${base}/healthz`),
      fetch(`${base}/.well-known/sophia.json`),
    ]);
    setStatus(health.ok && wellKnown.ok);
  } catch (error) {
    setStatus(false);
>>>>>>> origin/main
  }
}

function attachEvents() {
  elements.saveButton.addEventListener("click", () => {
    saveConfig();
  });
<<<<<<< HEAD
  elements.testConnector.addEventListener("click", () => {
    testConnectorConnection();
  });
=======
>>>>>>> origin/main
}

async function start() {
  attachEvents();
  await loadState();
  await pollHealth();
  setInterval(pollHealth, 5000);
}

start();
