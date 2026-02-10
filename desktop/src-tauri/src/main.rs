#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod state;

use state::{
    append_connector_event, find_free_port, load_config, save_config, spawn_gateway, ConnectorEnvelope,
    TerminalConfig, TerminalState,
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
fn save_terminal_config(state: State<TerminalState>, config: TerminalConfig) -> Result<(), String> {
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
        })
        .invoke_handler(tauri::generate_handler![
            get_terminal_state,
            save_terminal_config,
            log_connector_event
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
