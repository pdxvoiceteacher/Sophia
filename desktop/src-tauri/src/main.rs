#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod state;

use serde_json::Value;
use state::{
    append_connector_event, append_epoch_event, check_central_sync as check_central_sync_impl, find_free_port,
    guardrails_path, load_config, load_guardrails, save_config, spawn_gateway,
    test_connector_endpoint as test_connector_endpoint_impl, validate_market_flags, CentralSyncState,
    ConnectorEnvelope, ConnectorTestResult, EpochTestEnvelope, TerminalConfig, TerminalState,
};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
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
fn log_epoch_event(state: State<TerminalState>, envelope: EpochTestEnvelope) -> Result<(), String> {
    append_epoch_event(state.config_base.clone(), &envelope)
}

#[tauri::command]
fn test_connector_endpoint(endpoint: String) -> ConnectorTestResult {
    test_connector_endpoint_impl(&endpoint)
}

#[tauri::command]
fn check_central_sync(state: State<TerminalState>, central_url: String) -> Result<CentralSyncState, String> {
    check_central_sync_impl(&central_url, state.config_base.clone())
}

#[tauri::command]
fn run_epoch_test(state: State<TerminalState>, prompt_text: String, seed: i64) -> Result<EpochTestEnvelope, String> {
    let base_dir = dirs::home_dir().unwrap_or_else(|| PathBuf::from(".")).join(".sophia").join("epochs");
    fs::create_dir_all(&base_dir).map_err(|e| e.to_string())?;
    let stamp = chrono::Utc::now().format("%Y%m%dT%H%M%SZ").to_string();
    let run_root = base_dir.join(stamp);
    let baseline_dir = run_root.join("baseline");
    let exploratory_dir = run_root.join("exploratory");
    fs::create_dir_all(&baseline_dir).map_err(|e| e.to_string())?;
    fs::create_dir_all(&exploratory_dir).map_err(|e| e.to_string())?;

    let run_epoch = |mode: &str, out_dir: &PathBuf| -> Result<(), String> {
        let status = Command::new("python")
            .arg("tools/telemetry/run_epoch.py")
            .arg("--prompt-text")
            .arg(&prompt_text)
            .arg("--mode")
            .arg(mode)
            .arg("--seed")
            .arg(seed.to_string())
            .arg("--out")
            .arg(out_dir)
            .arg("--emit-tel")
            .arg("--emit-tel-events")
            .current_dir(&state.repo_root)
            .status()
            .map_err(|e| e.to_string())?;
        if status.success() {
            Ok(())
        } else {
            Err(format!("run_epoch_failed_{mode}"))
        }
    };

    run_epoch("deterministic", &baseline_dir)?;
    run_epoch("stochastic", &exploratory_dir)?;

    let analyze_status = Command::new("python")
        .arg("tools/telemetry/epoch_analyze.py")
        .arg("--run-dir")
        .arg(&exploratory_dir)
        .arg("--baseline-run-dir")
        .arg(&baseline_dir)
        .current_dir(&state.repo_root)
        .status()
        .map_err(|e| e.to_string())?;
    if !analyze_status.success() {
        return Err("epoch_analyze_failed".to_string());
    }

    let baseline_epoch: Value = serde_json::from_str(&fs::read_to_string(baseline_dir.join("epoch.json")).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let exploratory_epoch: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("epoch.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let exploratory_findings: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("epoch_findings.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;

    let findings = exploratory_findings
        .get("findings")
        .and_then(|v| v.as_array())
        .cloned()
        .unwrap_or_default();
    let entropy_spikes = findings
        .iter()
        .filter(|f| f.get("kind").and_then(|v| v.as_str()) == Some("entropy_spike"))
        .count();
    let branch_divergence = findings
        .iter()
        .any(|f| f.get("kind").and_then(|v| v.as_str()) == Some("branch_divergence"));
    let delta_psi_max = exploratory_findings
        .get("analysis")
        .and_then(|a| a.get("max_delta_psi"))
        .and_then(|v| v.as_f64())
        .unwrap_or(0.0);

    let baseline_metrics: Value = serde_json::from_str(
        &fs::read_to_string(baseline_dir.join("epoch_metrics.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let exploratory_metrics: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("epoch_metrics.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;

    let avg_es = |metrics: &Value| -> f64 {
        let series = metrics
            .get("step_series")
            .and_then(|v| v.as_array())
            .cloned()
            .unwrap_or_default();
        if series.is_empty() {
            return 0.0;
        }
        let total: f64 = series
            .iter()
            .map(|row| row.get("Es").and_then(|v| v.as_f64()).unwrap_or(0.0))
            .sum();
        total / series.len() as f64
    };

    Ok(EpochTestEnvelope {
        baseline_epoch_id: baseline_epoch
            .get("epoch_id")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string(),
        exploratory_epoch_id: exploratory_epoch
            .get("epoch_id")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string(),
        branch_divergence,
        entropy_spikes,
        delta_psi_max,
        es_drift: avg_es(&exploratory_metrics) - avg_es(&baseline_metrics),
        timestamp_utc: chrono::Utc::now().to_rfc3339(),
    })
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
            log_epoch_event,
            test_connector_endpoint,
            check_central_sync,
            run_epoch_test
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
