#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod state;

use state::{
    append_connector_event, check_central_sync as check_central_sync_impl, find_free_port, guardrails_path, load_config, load_guardrails,
    save_config, spawn_gateway, test_connector_endpoint as test_connector_endpoint_impl, validate_market_flags, CentralSyncState,
    ConnectorEnvelope, ConnectorTestResult, TerminalConfig, TerminalState,
};
use std::path::PathBuf;
use tauri::{Manager, State};

#[derive(serde::Serialize)]
struct TerminalStateResponse {
    port: u16,
    config: TerminalConfig,
}

#[tauri::command]
fn get_terminal_state(state: State<TerminalState>) -> TerminalStateResponse {
    let config = state
        .config
        .lock()
        .map(|guard| guard.clone())
        .unwrap_or_default();
    TerminalStateResponse {
        port: state.port,
        config,
    }
}

#[tauri::command]
fn validate_enabled_market_flags(state: State<TerminalState>, flags: Vec<String>) -> Result<(), String> {
    let path = guardrails_path(&state.repo_root);
    let guardrails = load_guardrails(&path).map_err(|err| format!("guardrails_load_failed: {err}"))?;
    validate_market_flags(&flags, &guardrails)
}

#[tauri::command]
fn save_terminal_config(state: State<TerminalState>, config: TerminalConfig) -> Result<(), String> {
    validate_enabled_market_flags(state.clone(), config.enabled_market_flags.clone())?;
    save_config(state.config_base.clone(), &config)?;
    if let Ok(mut guard) = state.config.lock() {
        *guard = config;
    }
    Ok(())
}

#[tauri::command]
fn log_connector_event(state: State<TerminalState>, envelope: ConnectorEnvelope) -> Result<(), String> {
    append_connector_event(state.config_base.clone(), &envelope)
}

#[tauri::command]
fn test_connector_endpoint(endpoint: String) -> ConnectorTestResult {
    test_connector_endpoint_impl(&endpoint)
}

#[tauri::command]
fn check_central_sync(state: State<TerminalState>, central_url: String) -> Result<CentralSyncState, String> {
    check_central_sync_impl(&central_url, state.config_base.clone())
}

fn repo_root() -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(|path| path.parent())
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."))
}

fn main() {
    let port = find_free_port(8001, 20).expect("No free port found");
    let repo_root = repo_root();
    let child = spawn_gateway(port, &repo_root).ok();
    let config = load_config(None);
    let config_base = None;

    tauri::Builder::default()
        .manage(TerminalState {
            port,
            config: std::sync::Mutex::new(config),
            child: std::sync::Mutex::new(child),
            config_base,
            repo_root,
        })
        .invoke_handler(tauri::generate_handler![
            get_terminal_state,
            validate_enabled_market_flags,
            save_terminal_config,
            log_connector_event,
            test_connector_endpoint,
            check_central_sync
        ])
        .on_window_event(|event| {
            if let tauri::WindowEvent::CloseRequested { .. } = event.event() {
                if let Some(state) = event.window().app_handle().try_state::<TerminalState>() {
                    state.stop_child();
                }
            }
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
