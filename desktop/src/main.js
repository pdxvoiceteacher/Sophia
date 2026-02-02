import { invoke } from "@tauri-apps/api/tauri";

const elements = {
  centralStandards: document.getElementById("central-standards"),
  localLlm: document.getElementById("local-llm"),
  gatewayPort: document.getElementById("gateway-port"),
  saveButton: document.getElementById("save-config"),
  saveStatus: document.getElementById("save-status"),
  gatewayStatus: document.getElementById("gateway-status"),
  viewerFrame: document.getElementById("viewer-frame"),
};

const state = {
  port: null,
  config: null,
};

function setStatus(ok) {
  elements.gatewayStatus.textContent = ok ? "Gateway: OK" : "Gateway: Down";
  elements.gatewayStatus.classList.toggle("ok", ok);
  elements.gatewayStatus.classList.toggle("down", !ok);
}

async function loadState() {
  const result = await invoke("get_terminal_state");
  state.port = result.port;
  state.config = result.config;
  elements.gatewayPort.value = String(state.port);
  elements.centralStandards.value = state.config.central_standards_url || "";
  elements.localLlm.value = state.config.local_llm_url || "";
  elements.viewerFrame.src = `http://127.0.0.1:${state.port}/sophia/viewer`;
}

async function saveConfig() {
  const payload = {
    central_standards_url: elements.centralStandards.value.trim(),
    local_llm_url: elements.localLlm.value.trim() || null,
  };
  await invoke("save_terminal_config", { config: payload });
  elements.saveStatus.textContent = "Saved";
  setTimeout(() => {
    elements.saveStatus.textContent = "";
  }, 1500);
}

async function pollHealth() {
  if (!state.port) return;
  try {
    const base = `http://127.0.0.1:${state.port}`;
    const [health, wellKnown] = await Promise.all([
      fetch(`${base}/healthz`),
      fetch(`${base}/.well-known/sophia.json`),
    ]);
    setStatus(health.ok && wellKnown.ok);
  } catch (error) {
    setStatus(false);
  }
}

function attachEvents() {
  elements.saveButton.addEventListener("click", () => {
    saveConfig();
  });
}

async function start() {
  attachEvents();
  await loadState();
  await pollHealth();
  setInterval(pollHealth, 5000);
}

start();
