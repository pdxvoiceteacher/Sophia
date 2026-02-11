#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod state;

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
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

#[derive(Serialize)]
struct TerminalStateResponse {
    port: u16,
    config: TerminalConfig,
}

#[derive(Serialize)]
struct SubmissionResult {
    submission_id: String,
    submission_path: String,
    bundle_path: String,
    posted: bool,
    detail: String,
}

#[derive(Serialize)]
struct AttestationResult {
    submission_id: String,
    attestation_path: String,
    detail: String,
}

#[derive(Deserialize)]
struct BuildSubmissionResult {
    submission_path: String,
    bundle_path: String,
}

fn sophia_home() -> PathBuf {
    dirs::home_dir().unwrap_or_else(|| PathBuf::from(".")).join(".sophia")
}

fn run_python(repo_root: &PathBuf, args: &[&str]) -> Result<(), String> {
    let status = Command::new("python")
        .args(args)
        .current_dir(repo_root)
        .status()
        .map_err(|e| e.to_string())?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("python_command_failed: {:?}", args))
    }
}


fn validate_attestation_file(repo_root: &PathBuf, attestation_path: &PathBuf) -> Result<(), String> {
    run_python(
        repo_root,
        &[
            "tools/telemetry/validate_attestations.py",
            "--schema",
            "schema/attestations_v1.schema.json",
            "--path",
            attestation_path.to_string_lossy().as_ref(),
        ],
    )
}

fn scenario_json_path(repo_root: &PathBuf, scenario_name: &str) -> Result<PathBuf, String> {
    let path = repo_root.join("epoch_scenarios").join(scenario_name);
    if path.exists() {
        Ok(path)
    } else {
        Err(format!("scenario_not_found: {scenario_name}"))
    }
}

#[tauri::command]
fn get_terminal_state(state: State<TerminalState>) -> TerminalStateResponse {
    let config = state
        .config
        .lock()
        .map(|guard| guard.clone())
        .unwrap_or_default();
    TerminalStateResponse { port: state.port, config }
}

#[tauri::command]
fn list_epoch_scenarios(state: State<TerminalState>) -> Result<Vec<String>, String> {
    let scenarios_dir = state.repo_root.join("epoch_scenarios");
    let mut out: Vec<String> = fs::read_dir(scenarios_dir)
        .map_err(|e| e.to_string())?
        .filter_map(|entry| entry.ok())
        .filter_map(|entry| {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("json") {
                path.file_name().and_then(|n| n.to_str()).map(|n| n.to_string())
            } else {
                None
            }
        })
        .collect();
    out.sort();
    Ok(out)
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
fn run_epoch_test(
    state: State<TerminalState>,
    baseline_scenario: String,
    experimental_scenario: String,
    seed: i64,
) -> Result<EpochTestEnvelope, String> {
    let base_dir = sophia_home().join("epochs");
    fs::create_dir_all(&base_dir).map_err(|e| e.to_string())?;
    let stamp = chrono::Utc::now().format("%Y%m%dT%H%M%SZ").to_string();
    let run_root = base_dir.join(stamp);
    let baseline_dir = run_root.join("baseline");
    let exploratory_dir = run_root.join("experimental");
    fs::create_dir_all(&baseline_dir).map_err(|e| e.to_string())?;
    fs::create_dir_all(&exploratory_dir).map_err(|e| e.to_string())?;

    let baseline_path = scenario_json_path(&state.repo_root, &baseline_scenario)?;
    let experimental_path = scenario_json_path(&state.repo_root, &experimental_scenario)?;

    run_python(
        &state.repo_root,
        &[
            "tools/telemetry/run_epoch_real.py",
            "--scenario",
            baseline_path.to_string_lossy().as_ref(),
            "--mode",
            "deterministic",
            "--seed",
            &seed.to_string(),
            "--out",
            baseline_dir.to_string_lossy().as_ref(),
            "--emit-tel",
            "--emit-tel-events",
        ],
    )?;

    run_python(
        &state.repo_root,
        &[
            "tools/telemetry/run_epoch_real.py",
            "--scenario",
            experimental_path.to_string_lossy().as_ref(),
            "--mode",
            "stochastic",
            "--seed",
            &seed.to_string(),
            "--out",
            exploratory_dir.to_string_lossy().as_ref(),
            "--baseline-run-dir",
            baseline_dir.to_string_lossy().as_ref(),
            "--emit-tel",
            "--emit-tel-events",
        ],
    )?;

    let baseline_epoch: Value = serde_json::from_str(&fs::read_to_string(baseline_dir.join("epoch.json")).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let exploratory_epoch: Value = serde_json::from_str(&fs::read_to_string(exploratory_dir.join("epoch.json")).map_err(|e| e.to_string())?)
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

    let baseline_tel_hash = exploratory_findings
        .get("analysis")
        .and_then(|a| a.get("baseline_tel_hash"))
        .and_then(|v| v.as_str())
        .map(|v| v.to_string());
    let experimental_tel_hash = exploratory_findings
        .get("analysis")
        .and_then(|a| a.get("tel_hash"))
        .and_then(|v| v.as_str())
        .map(|v| v.to_string());

    let baseline_metrics: Value = serde_json::from_str(
        &fs::read_to_string(baseline_dir.join("epoch_metrics.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let exploratory_metrics: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("epoch_metrics.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;


    let sentinel_doc: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("sentinel_state.json")).unwrap_or_else(|_| {
            "{\"state\":\"normal\",\"reasons\":[]}".to_string()
        }),
    )
    .unwrap_or_else(|_| json!({"state": "normal", "reasons": []}));
    let sentinel_state = sentinel_doc
        .get("state")
        .and_then(|v| v.as_str())
        .unwrap_or("normal")
        .to_string();
    let sentinel_reason_count = sentinel_doc
        .get("reasons")
        .and_then(|v| v.as_array())
        .map(|items| items.len())
        .unwrap_or(0);

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
        baseline_epoch_id: baseline_epoch.get("epoch_id").and_then(|v| v.as_str()).unwrap_or("unknown").to_string(),
        exploratory_epoch_id: exploratory_epoch
            .get("epoch_id")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string(),
        baseline_tel_hash: baseline_tel_hash.clone(),
        experimental_tel_hash: experimental_tel_hash.clone(),
        tel_hash_equal: baseline_tel_hash.is_some() && baseline_tel_hash == experimental_tel_hash,
        branch_divergence,
        entropy_spikes,
        delta_psi_max,
        es_drift: avg_es(&exploratory_metrics) - avg_es(&baseline_metrics),
        sentinel_state,
        sentinel_reason_count,
        run_folder: run_root.to_string_lossy().to_string(),
        timestamp_utc: chrono::Utc::now().to_rfc3339(),
    })
}

#[tauri::command]
fn create_cross_review_submission(
    state: State<TerminalState>,
    run_folder: String,
    submitter_id: Option<String>,
    central_url: Option<String>,
) -> Result<SubmissionResult, String> {
    let submission_id = format!("sub-{}", chrono::Utc::now().format("%Y%m%dT%H%M%SZ"));
    let submissions_dir = sophia_home().join("submissions").join(&submission_id);
    fs::create_dir_all(&submissions_dir).map_err(|e| e.to_string())?;

    let run_dir = PathBuf::from(run_folder);
    run_python(
        &state.repo_root,
        &[
            "tools/telemetry/build_review_bundle.py",
            "--run-dir",
            run_dir.to_string_lossy().as_ref(),
            "--out-dir",
            submissions_dir.to_string_lossy().as_ref(),
            "--submission-id",
            &submission_id,
            "--submitter-id",
            submitter_id.as_deref().unwrap_or("local-operator"),
        ],
    )?;

    let build_result_path = submissions_dir.join("build_result.json");
    let build: BuildSubmissionResult = serde_json::from_str(
        &fs::read_to_string(&build_result_path).map_err(|e| format!("build_result_missing: {e}"))?,
    )
    .map_err(|e| e.to_string())?;

    let mut posted = false;
    let mut detail = "created_local_bundle".to_string();
    if let Some(url) = central_url {
        if !url.trim().is_empty() {
            let client = reqwest::blocking::Client::builder()
                .timeout(std::time::Duration::from_secs(10))
                .build()
                .map_err(|e| e.to_string())?;
            let submission_payload = json!({
                "submission_id": submission_id,
                "submission_path": build.submission_path,
                "bundle_path": build.bundle_path,
            });
            match client
                .post(format!("{}/review/submissions", url.trim_end_matches('/')))
                .json(&submission_payload)
                .send()
            {
                Ok(resp) => {
                    posted = resp.status().is_success();
                    detail = format!("central_post_http_{}", resp.status());
                }
                Err(err) => {
                    detail = format!("central_post_failed: {err}");
                }
            }
        }
    }

    Ok(SubmissionResult {
        submission_id,
        submission_path: build.submission_path,
        bundle_path: build.bundle_path,
        posted,
        detail,
    })
}

#[tauri::command]
fn fetch_attestations(
    _state: State<TerminalState>,
    submission_id: String,
    central_url: Option<String>,
) -> Result<AttestationResult, String> {
    let att_dir = sophia_home().join("attestations");
    fs::create_dir_all(&att_dir).map_err(|e| e.to_string())?;
    let att_path = att_dir.join(format!("{submission_id}.json"));

    let detail = if let Some(url) = central_url {
        if !url.trim().is_empty() {
            let client = reqwest::blocking::Client::builder()
                .timeout(std::time::Duration::from_secs(10))
                .build()
                .map_err(|e| e.to_string())?;
            match client
                .get(format!("{}/review/attestations/{}", url.trim_end_matches('/'), submission_id))
                .send()
            {
                Ok(resp) if resp.status().is_success() => {
                    let body = resp.text().map_err(|e| e.to_string())?;
                    let mut parsed: Value = serde_json::from_str(&body).map_err(|e| format!("invalid_attestation_json: {e}"))?;
                    if parsed.get("schema").is_none() {
                        if let Some(obj) = parsed.as_object_mut() {
                            obj.insert("schema".to_string(), Value::String("attestations_v1".to_string()));
                        }
                    }
                    fs::write(&att_path, serde_json::to_string_pretty(&parsed).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
                    "fetched_from_central".to_string()
                }
                Ok(resp) => {
                    let stub = json!({
                        "schema": "attestations_v1",
                        "submission_id": submission_id,
                        "status": "pending",
                        "reviewer": "central_stub",
                        "detail": format!("attestation_http_{}", resp.status())
                    });
                    fs::write(&att_path, serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?)
                        .map_err(|e| e.to_string())?;
                    format!("central_http_{}", resp.status())
                }
                Err(err) => {
                    let stub = json!({
                        "schema": "attestations_v1",
                        "submission_id": submission_id,
                        "status": "pending",
                        "reviewer": "local_stub",
                        "detail": format!("fetch_failed: {err}")
                    });
                    fs::write(&att_path, serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?)
                        .map_err(|e| e.to_string())?;
                    "created_local_stub_after_failure".to_string()
                }
            }
        } else {
            let stub = json!({
                "schema": "attestations_v1",
                "submission_id": submission_id,
                "status": "pending",
                "reviewer": "local_stub",
                "detail": "no_central_url"
            });
            fs::write(&att_path, serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
            "created_local_stub".to_string()
        }
    } else {
        let stub = json!({
            "submission_id": submission_id,
            "status": "pending",
            "reviewer": "local_stub",
            "detail": "no_central_url"
        });
        fs::write(&att_path, serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        "created_local_stub".to_string()
    };

    validate_attestation_file(&state.repo_root, &att_path)?;

    Ok(AttestationResult {
        submission_id,
        attestation_path: att_path.to_string_lossy().to_string(),
        detail,
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
            list_epoch_scenarios,
            validate_enabled_market_flags,
            save_terminal_config,
            log_connector_event,
            log_epoch_event,
            test_connector_endpoint,
            check_central_sync,
            run_epoch_test,
            create_cross_review_submission,
            fetch_attestations
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
