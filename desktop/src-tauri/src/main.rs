#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod state;

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use state::{
    append_connector_event, append_epoch_event, check_central_sync as check_central_sync_impl,
    find_free_port, get_active_connector, guardrails_path, load_config, load_guardrails,
    save_config, spawn_gateway, test_connector_endpoint as test_connector_endpoint_impl,
    validate_market_flags, CentralSyncState, ConnectorConfig, ConnectorEnvelope,
    ConnectorTestResult, EpochTestEnvelope, TerminalConfig, TerminalState,
};
use std::collections::BTreeMap;
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
struct ActiveConnectorResponse {
    connector: Option<ConnectorConfig>,
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
struct AttestationSummary {
    total: usize,
    pass: usize,
    fail: usize,
    pending: usize,
    latest_timestamp: Option<String>,
}

#[derive(Serialize)]
struct AttestationResult {
    submission_id: String,
    attestation_path: String,
    detail: String,
    summary: AttestationSummary,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PeerNode {
    node_id: String,
    endpoint: String,
    pubkey: String,
    trust_weight: f64,
    #[serde(default = "default_peer_trust_tier")]
    trust_tier: String,
    #[serde(default = "default_allowed_policy_profiles")]
    allowed_policy_profiles: Vec<String>,
    enabled: bool,
}

fn default_peer_trust_tier() -> String {
    "witness".to_string()
}

fn default_allowed_policy_profiles() -> Vec<String> {
    vec!["witness_only".to_string(), "reproducible_audit".to_string()]
}

#[derive(Serialize)]
struct PeerListResponse {
    peers: Vec<PeerNode>,
}

#[derive(Serialize)]
struct PeerAttestationResponse {
    attestation: Value,
    consensus: String,
    divergence_count: usize,
    total_peers: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct NetworkEncryption {
    alg: String,
    key_wrap: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct NetworkRelayToggles {
    evidence_full_relay: bool,
    vault_relay: bool,
}

fn default_network_relay_toggles() -> NetworkRelayToggles {
    NetworkRelayToggles {
        evidence_full_relay: false,
        vault_relay: false,
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct NetworkPolicy {
    schema: String,
    profile: String,
    share_scopes: Vec<String>,
    encryption: NetworkEncryption,
    peer_set: Vec<String>,
    #[serde(default = "default_network_relay_toggles")]
    relay_toggles: NetworkRelayToggles,
}

#[derive(Serialize)]
struct NetworkPolicyResponse {
    policy: NetworkPolicy,
    network_required: bool,
    degraded_mode: bool,
    reason: String,
}

fn default_network_policy() -> NetworkPolicy {
    NetworkPolicy {
        schema: "network_policy_v1".to_string(),
        profile: "witness_only".to_string(),
        share_scopes: vec![
            "hashes/*".to_string(),
            "metrics/*".to_string(),
            "attestations/*".to_string(),
        ],
        encryption: NetworkEncryption {
            alg: "AES-256-GCM".to_string(),
            key_wrap: "X25519-sealed-box".to_string(),
        },
        peer_set: vec![],
        relay_toggles: default_network_relay_toggles(),
    }
}

fn allowed_share_scopes() -> &'static [&'static str] {
    &[
        "hashes/*",
        "metrics/*",
        "attestations/*",
        "tel/*",
        "evidence/*",
        "vault/*",
    ]
}

fn scope_in(scope: &str, prefix: &str) -> bool {
    scope.trim().eq_ignore_ascii_case(prefix)
}

fn has_scope(scopes: &[String], prefix: &str) -> bool {
    scopes.iter().any(|item| scope_in(item, prefix))
}

fn scope_allowed(scope: &str) -> bool {
    allowed_share_scopes()
        .iter()
        .any(|allowed| scope_in(scope, allowed))
}

fn canonicalize_json(value: &Value) -> Value {
    match value {
        Value::Object(map) => {
            let mut sorted: BTreeMap<String, Value> = BTreeMap::new();
            for (key, nested) in map {
                sorted.insert(key.clone(), canonicalize_json(nested));
            }
            let mut out = serde_json::Map::new();
            for (key, nested) in sorted {
                out.insert(key, nested);
            }
            Value::Object(out)
        }
        Value::Array(items) => Value::Array(items.iter().map(canonicalize_json).collect()),
        _ => value.clone(),
    }
}

fn canonical_sha256_hex(value: &Value) -> String {
    let canonical = canonicalize_json(value);
    let bytes = serde_json::to_vec(&canonical).unwrap_or_default();
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

#[derive(Deserialize)]
struct BuildSubmissionResult {
    submission_path: String,
    bundle_path: String,
}

fn sophia_home() -> PathBuf {
    dirs::home_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join(".sophia")
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

fn run_python_with_env(
    repo_root: &PathBuf,
    args: &[&str],
    env_pairs: &[(String, String)],
) -> Result<(), String> {
    let mut command = Command::new("python");
    command.args(args).current_dir(repo_root);
    for (key, value) in env_pairs {
        command.env(key, value);
    }
    let status = command.status().map_err(|e| e.to_string())?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("python_command_failed: {:?}", args))
    }
}

fn validate_attestation_file(
    repo_root: &PathBuf,
    attestation_path: &PathBuf,
) -> Result<(), String> {
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

fn summarize_attestations(payload: &Value) -> AttestationSummary {
    let items: Vec<&Value> = if let Some(array) = payload.as_array() {
        array.iter().collect()
    } else if let Some(array) = payload.get("attestations").and_then(|v| v.as_array()) {
        array.iter().collect()
    } else {
        vec![payload]
    };

    let mut pass = 0;
    let mut fail = 0;
    let mut pending = 0;
    let mut latest_timestamp: Option<String> = None;

    for item in items.iter().filter(|v| !v.is_null()) {
        let status = item
            .get("status")
            .and_then(|v| v.as_str())
            .unwrap_or("pending")
            .to_lowercase();
        if status == "pass" {
            pass += 1;
        } else if status == "fail" {
            fail += 1;
        } else {
            pending += 1;
        }

        let ts = item
            .get("timestamp_utc")
            .or_else(|| item.get("timestamp"))
            .or_else(|| item.get("reviewed_at"))
            .and_then(|v| v.as_str())
            .map(str::to_string);
        if let Some(ts) = ts {
            let should_update = match latest_timestamp.as_ref() {
                Some(current) => ts > *current,
                None => true,
            };
            if should_update {
                latest_timestamp = Some(ts);
            }
        }
    }

    AttestationSummary {
        total: pass + fail + pending,
        pass,
        fail,
        pending,
        latest_timestamp,
    }
}

fn peer_registry_repo_path(repo_root: &PathBuf) -> PathBuf {
    repo_root.join("config").join("peer_registry_v1.json")
}

fn network_policy_repo_path(repo_root: &PathBuf) -> PathBuf {
    repo_root.join("config").join("network_policy_v1.json")
}

fn network_policy_local_path() -> PathBuf {
    sophia_home().join("network_policy_local.json")
}

fn load_network_policy(state: &TerminalState) -> NetworkPolicy {
    let mut policy = default_network_policy();
    let repo_path = network_policy_repo_path(&state.repo_root);
    if let Ok(text) = fs::read_to_string(repo_path) {
        if let Ok(parsed) = serde_json::from_str::<NetworkPolicy>(&text) {
            policy = parsed;
        }
    }
    let local_path = network_policy_local_path();
    if let Ok(text) = fs::read_to_string(local_path) {
        if let Ok(parsed) = serde_json::from_str::<NetworkPolicy>(&text) {
            policy = parsed;
        }
    }
    policy
}

fn save_local_network_policy(policy: &NetworkPolicy) -> Result<(), String> {
    let path = network_policy_local_path();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    fs::write(
        path,
        serde_json::to_string_pretty(policy).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

fn env_network_required() -> bool {
    std::env::var("SOPHIA_NETWORK_REQUIRED")
        .map(|value| {
            let normalized = value.trim().to_ascii_lowercase();
            normalized == "1" || normalized == "true" || normalized == "yes"
        })
        .unwrap_or(false)
}

fn env_allow_witness_only_when_network_required() -> bool {
    std::env::var("SOPHIA_ALLOW_WITNESS_ONLY_WHEN_REQUIRED")
        .map(|value| {
            let normalized = value.trim().to_ascii_lowercase();
            normalized == "1" || normalized == "true" || normalized == "yes"
        })
        .unwrap_or(false)
}

fn evaluate_network_mode(state: &TerminalState) -> (bool, String) {
    let network_required = env_network_required();
    let peers = load_peer_registry(state);
    let enabled_peers = peers.iter().filter(|p| p.enabled).count();
    if network_required && enabled_peers == 0 {
        return (true, "network_required_but_no_enabled_peers".to_string());
    }
    if enabled_peers == 0 {
        return (true, "offline_local_mode".to_string());
    }
    (false, "peer_network_available".to_string())
}

fn peer_registry_local_path() -> PathBuf {
    sophia_home().join("peer_registry_local.json")
}

fn load_peer_registry(state: &TerminalState) -> Vec<PeerNode> {
    let mut peers: Vec<PeerNode> = Vec::new();
    let repo_path = peer_registry_repo_path(&state.repo_root);
    if let Ok(text) = fs::read_to_string(repo_path) {
        if let Ok(payload) = serde_json::from_str::<Value>(&text) {
            if let Some(items) = payload.get("peers").and_then(|v| v.as_array()) {
                for item in items {
                    if let Ok(peer) = serde_json::from_value::<PeerNode>(item.clone()) {
                        peers.push(peer);
                    }
                }
            }
        }
    }

    let local_path = peer_registry_local_path();
    if let Ok(text) = fs::read_to_string(local_path) {
        if let Ok(payload) = serde_json::from_str::<Value>(&text) {
            if let Some(items) = payload.get("peers").and_then(|v| v.as_array()) {
                for item in items {
                    if let Ok(peer) = serde_json::from_value::<PeerNode>(item.clone()) {
                        if !peers.iter().any(|p| p.node_id == peer.node_id) {
                            peers.push(peer);
                        }
                    }
                }
            }
        }
    }
    peers
}

fn save_local_peer_registry(peers: &[PeerNode]) -> Result<(), String> {
    let path = peer_registry_local_path();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    let payload = json!({"schema": "peer_registry_v1", "peers": peers});
    fs::write(
        path,
        serde_json::to_string_pretty(&payload).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

fn build_peer_attestation(
    node: &PeerNode,
    bundle_hash: &str,
    checks_run: &[String],
    results: Value,
) -> Value {
    let timestamp = chrono::Utc::now().to_rfc3339();
    // TODO(crypto): replace demo signature scaffold with real Ed25519 signing and key management.
    // Signatures MUST be computed over canonical JSON (sorted keys + stable list ordering)
    // or a stable hash derived from that canonical form.
    let signature_alg = "demo-ed25519-placeholder";
    let signing_preimage = json!({
        "schema": "peer_attestation_v1",
        "node_id": node.node_id,
        "pubkey": node.pubkey,
        "pubkey_format": "base64",
        "bundle_hash": bundle_hash,
        "checks_run": checks_run,
        "results": results,
        "timestamp_utc": timestamp,
        "signature_alg": signature_alg,
        "signature_format": "base64"
    });
    let signed_bytes_hash = canonical_sha256_hex(&signing_preimage);
    let signature = format!("demo-sig:{}", signed_bytes_hash);
    let mut attestation = signing_preimage;
    if let Some(obj) = attestation.as_object_mut() {
        obj.insert(
            "signed_bytes_hash".to_string(),
            Value::String(signed_bytes_hash),
        );
        obj.insert("signature".to_string(), Value::String(signature));
    }
    attestation
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
    TerminalStateResponse {
        port: state.port,
        config,
    }
}

#[tauri::command]
fn get_active_connector_config(state: State<TerminalState>) -> ActiveConnectorResponse {
    let config = state
        .config
        .lock()
        .map(|guard| guard.clone())
        .unwrap_or_default();
    ActiveConnectorResponse {
        connector: get_active_connector(&config),
    }
}

#[tauri::command]
fn list_peers(state: State<TerminalState>) -> PeerListResponse {
    PeerListResponse {
        peers: load_peer_registry(&state),
    }
}

#[tauri::command]
fn add_peer(
    state: State<TerminalState>,
    node_id: String,
    endpoint: String,
    pubkey: String,
    trust_weight: f64,
) -> Result<PeerListResponse, String> {
    let mut peers = load_peer_registry(&state);
    if let Some(existing) = peers.iter_mut().find(|p| p.node_id == node_id) {
        existing.endpoint = endpoint;
        existing.pubkey = pubkey;
        existing.trust_weight = trust_weight;
        existing.enabled = true;
    } else {
        peers.push(PeerNode {
            node_id,
            endpoint,
            pubkey,
            trust_weight,
            enabled: true,
        });
    }
    save_local_peer_registry(&peers)?;
    Ok(PeerListResponse { peers })
}

#[tauri::command]
fn request_peer_attestation(
    state: State<TerminalState>,
    peer_id: String,
    bundle_hash: String,
    checks_run: Vec<String>,
    run_folder: Option<String>,
) -> Result<PeerAttestationResponse, String> {
    let peers = load_peer_registry(&state);
    let network_policy = load_network_policy(&state);
    let network_required = env_network_required();
    let (degraded_mode, reason) = evaluate_network_mode(&state);
    if network_required && degraded_mode {
        return Err(format!("network_required_blocked: {reason}"));
    }
    let peer = peers
        .iter()
        .find(|p| p.node_id == peer_id && p.enabled)
        .cloned()
        .ok_or_else(|| "peer_not_found_or_disabled".to_string())?;

    if !network_policy.peer_set.is_empty()
        && !network_policy
            .peer_set
            .iter()
            .any(|item| item == &peer.node_id)
    {
        return Err("peer_not_authorized_by_network_policy".to_string());
    }
    if !peer
        .allowed_policy_profiles
        .iter()
        .any(|item| item == &network_policy.profile)
    {
        return Err("peer_not_allowed_for_selected_network_profile".to_string());
    }
    if network_policy.profile == "full_relay" && peer.trust_tier != "full_relay" {
        return Err("full_relay_requires_full_relay_trust_tier".to_string());
    }

    let remote_result = if !peer.endpoint.trim().is_empty() {
        let client = reqwest::blocking::Client::builder()
            .timeout(std::time::Duration::from_secs(10))
            .build()
            .map_err(|e| e.to_string())?;
        let payload = json!({
            "bundle_hash": bundle_hash,
            "checks_run": checks_run,
        });
        match client
            .post(format!(
                "{}/sonya/attest",
                peer.endpoint.trim_end_matches('/')
            ))
            .json(&payload)
            .send()
        {
            Ok(resp) if resp.status().is_success() => {
                serde_json::from_str::<Value>(&resp.text().map_err(|e| e.to_string())?)
                    .unwrap_or_else(
                        |_| json!({"status": "pass", "source": "remote_parse_fallback"}),
                    )
            }
            _ => json!({"status": "pass", "source": "local_fallback"}),
        }
    } else {
        json!({"status": "pass", "source": "local_peer"})
    };

    let attestation = build_peer_attestation(&peer, &bundle_hash, &checks_run, remote_result);

    if let Some(run_folder) = run_folder {
        let run_dir = PathBuf::from(run_folder);
        if run_dir.exists() {
            let path = run_dir.join("peer_attestations.json");
            let mut attestations = if let Ok(raw) = fs::read_to_string(&path) {
                serde_json::from_str::<Value>(&raw).unwrap_or_else(|_| json!({"attestations": []}))
            } else {
                json!({"schema": "peer_attestations_v1", "attestations": []})
            };
            if let Some(items) = attestations
                .get_mut("attestations")
                .and_then(|v| v.as_array_mut())
            {
                items.push(attestation.clone());
            }
            fs::write(
                &path,
                serde_json::to_string_pretty(&attestations).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?;

            let epoch_path = run_dir.join("epoch.json");
            if epoch_path.exists() {
                if let Ok(epoch_raw) = fs::read_to_string(&epoch_path) {
                    if let Ok(mut epoch_doc) = serde_json::from_str::<Value>(&epoch_raw) {
                        if let Some(outputs) = epoch_doc
                            .get_mut("outputs_manifest")
                            .and_then(|v| v.as_object_mut())
                        {
                            outputs.insert(
                                "peer_attestations.json".to_string(),
                                json!({"attached": true, "source": path.to_string_lossy()}),
                            );
                            let _ = fs::write(
                                &epoch_path,
                                serde_json::to_string_pretty(&epoch_doc)
                                    .map_err(|e| e.to_string())?,
                            );
                        }
                    }
                }
            }
        }
    }

    let divergence_count = if attestation
        .get("results")
        .and_then(|v| v.get("status"))
        .and_then(|v| v.as_str())
        == Some("pass")
    {
        0
    } else {
        1
    };
    let consensus = if divergence_count == 0 {
        "convergent"
    } else {
        "divergent"
    }
    .to_string();

    Ok(PeerAttestationResponse {
        attestation,
        consensus,
        divergence_count,
        total_peers: peers.iter().filter(|p| p.enabled).count(),
    })
}

#[tauri::command]
fn get_network_policy(state: State<TerminalState>) -> NetworkPolicyResponse {
    let policy = load_network_policy(&state);
    let network_required = env_network_required();
    let (degraded_mode, reason) = evaluate_network_mode(&state);
    NetworkPolicyResponse {
        policy,
        network_required,
        degraded_mode,
        reason,
    }
}

#[tauri::command]
fn save_network_policy(
    state: State<TerminalState>,
    profile: String,
    share_scopes: Vec<String>,
    peer_set: Vec<String>,
) -> Result<NetworkPolicyResponse, String> {
    let mut policy = load_network_policy(&state);
    let valid_profiles = ["witness_only", "reproducible_audit", "full_relay"];
    if !valid_profiles.iter().any(|item| item == &profile) {
        return Err("invalid_network_profile".to_string());
    }

    for scope in &share_scopes {
        if !scope_allowed(scope) {
            return Err(format!("invalid_share_scope: {scope}"));
        }
    }

    let network_required = env_network_required();
    if network_required
        && profile == "witness_only"
        && !env_allow_witness_only_when_network_required()
    {
        return Err("network_required_forbids_witness_only_profile".to_string());
    }

    if profile == "witness_only" {
        if has_scope(&share_scopes, "vault/*") || has_scope(&share_scopes, "evidence/*") {
            return Err("witness_only_disallows_vault_and_evidence_scopes".to_string());
        }
    }

    if profile == "reproducible_audit" && has_scope(&share_scopes, "vault/*") {
        return Err("reproducible_audit_disallows_vault_scope".to_string());
    }

    if profile == "full_relay" && peer_set.is_empty() {
        return Err("full_relay_requires_non_empty_peer_set".to_string());
    }

    if profile == "full_relay" {
        let peers = load_peer_registry(&state);
        let eligible = peers.iter().any(|peer| {
            peer.enabled
                && peer.trust_tier == "full_relay"
                && (peer_set.is_empty() || peer_set.iter().any(|id| id == &peer.node_id))
        });
        if !eligible {
            return Err("full_relay_requires_full_relay_eligible_peer".to_string());
        }
    }

    let relay_toggles = NetworkRelayToggles {
        evidence_full_relay: has_scope(&share_scopes, "evidence/*"),
        vault_relay: has_scope(&share_scopes, "vault/*"),
    };

    if relay_toggles.vault_relay && profile != "full_relay" {
        return Err("vault_scope_requires_full_relay_profile".to_string());
    }

    let (degraded_mode, reason) = evaluate_network_mode(&state);
    if network_required && degraded_mode && profile == "full_relay" {
        return Err(format!("network_required_blocked: {reason}"));
    }

    policy.profile = profile;
    policy.share_scopes = share_scopes;
    policy.peer_set = peer_set;
    policy.relay_toggles = relay_toggles;
    save_local_network_policy(&policy)?;
    let (degraded_mode, reason) = evaluate_network_mode(&state);
    Ok(NetworkPolicyResponse {
        policy,
        network_required,
        degraded_mode,
        reason,
    })
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
                path.file_name()
                    .and_then(|n| n.to_str())
                    .map(|n| n.to_string())
            } else {
                None
            }
        })
        .collect();
    out.sort();
    Ok(out)
}

#[tauri::command]
fn validate_enabled_market_flags(
    state: State<TerminalState>,
    flags: Vec<String>,
) -> Result<(), String> {
    let path = guardrails_path(&state.repo_root);
    let guardrails =
        load_guardrails(&path).map_err(|err| format!("guardrails_load_failed: {err}"))?;
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
fn log_connector_event(
    state: State<TerminalState>,
    envelope: ConnectorEnvelope,
) -> Result<(), String> {
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
fn check_central_sync(
    state: State<TerminalState>,
    central_url: String,
) -> Result<CentralSyncState, String> {
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

    let active_connector = state
        .config
        .lock()
        .ok()
        .and_then(|cfg| get_active_connector(&cfg));
    let mut connector_env: Vec<(String, String)> = Vec::new();
    if let Some(connector) = active_connector {
        connector_env.push((
            "SOPHIA_CONNECTOR_TYPE".to_string(),
            connector.connector_type,
        ));
        if let Some(endpoint) = connector.connector_endpoint {
            connector_env.push(("SOPHIA_CONNECTOR_ENDPOINT".to_string(), endpoint));
        }
        if let Some(model) = connector.connector_model {
            connector_env.push(("SOPHIA_CONNECTOR_MODEL".to_string(), model));
        }
    }

    run_python_with_env(
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
        &connector_env,
    )?;

    run_python_with_env(
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
        &connector_env,
    )?;

    let baseline_epoch: Value = serde_json::from_str(
        &fs::read_to_string(baseline_dir.join("epoch.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let exploratory_epoch: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("epoch.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let exploratory_findings: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("epoch_findings.json"))
            .map_err(|e| e.to_string())?,
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
        &fs::read_to_string(exploratory_dir.join("epoch_metrics.json"))
            .map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;

    let sentinel_doc: Value = serde_json::from_str(
        &fs::read_to_string(exploratory_dir.join("sentinel_state.json"))
            .unwrap_or_else(|_| "{\"state\":\"normal\",\"reasons\":[]}".to_string()),
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
        &fs::read_to_string(&build_result_path)
            .map_err(|e| format!("build_result_missing: {e}"))?,
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
        summary,
    })
}

#[tauri::command]
fn fetch_attestations(
    state: State<TerminalState>,
    submission_id: String,
    central_url: Option<String>,
    run_folder: Option<String>,
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
                .get(format!(
                    "{}/review/attestations/{}",
                    url.trim_end_matches('/'),
                    submission_id
                ))
                .send()
            {
                Ok(resp) if resp.status().is_success() => {
                    let body = resp.text().map_err(|e| e.to_string())?;
                    let mut parsed: Value = serde_json::from_str(&body)
                        .map_err(|e| format!("invalid_attestation_json: {e}"))?;
                    if parsed.get("schema").is_none() {
                        if let Some(obj) = parsed.as_object_mut() {
                            obj.insert(
                                "schema".to_string(),
                                Value::String("attestations_v1".to_string()),
                            );
                        }
                    }
                    fs::write(
                        &att_path,
                        serde_json::to_string_pretty(&parsed).map_err(|e| e.to_string())?,
                    )
                    .map_err(|e| e.to_string())?;
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
                    fs::write(
                        &att_path,
                        serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?,
                    )
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
                    fs::write(
                        &att_path,
                        serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?,
                    )
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
            fs::write(
                &att_path,
                serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?,
            )
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
        fs::write(
            &att_path,
            serde_json::to_string_pretty(&stub).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        "created_local_stub".to_string()
    };

    validate_attestation_file(&state.repo_root, &att_path)?;

    let summary_payload: Value =
        serde_json::from_str(&fs::read_to_string(&att_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let summary = summarize_attestations(&summary_payload);

    if let Some(run_folder) = run_folder {
        let run_dir = PathBuf::from(run_folder);
        if run_dir.exists() {
            let run_attestations = run_dir.join("attestations.json");
            fs::write(
                &run_attestations,
                serde_json::to_string_pretty(&summary_payload).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?;

            let epoch_path = run_dir.join("epoch.json");
            if epoch_path.exists() {
                if let Ok(epoch_raw) = fs::read_to_string(&epoch_path) {
                    if let Ok(mut epoch_doc) = serde_json::from_str::<Value>(&epoch_raw) {
                        if let Some(outputs) = epoch_doc
                            .get_mut("outputs_manifest")
                            .and_then(|v| v.as_object_mut())
                        {
                            outputs.insert(
                                "attestations.json".to_string(),
                                json!({"attached": true, "source": run_attestations.to_string_lossy()}),
                            );
                            let _ = fs::write(
                                &epoch_path,
                                serde_json::to_string_pretty(&epoch_doc)
                                    .map_err(|e| e.to_string())?,
                            );
                        }
                    }
                }
            }
        }
    }

    Ok(AttestationResult {
        submission_id,
        attestation_path: att_path.to_string_lossy().to_string(),
        detail,
        summary,
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
            get_active_connector_config,
            get_network_policy,
            save_network_policy,
            list_peers,
            add_peer,
            request_peer_attestation,
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
