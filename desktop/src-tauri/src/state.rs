use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use std::path::PathBuf;
use std::process::{Child, Command};
use std::sync::Mutex;
use std::time::{Duration, Instant};
use tauri::api::path::home_dir;
use url::Url;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TerminalConfig {
    pub central_standards_url: String,
    pub local_llm_url: Option<String>,
    pub connector_type: String,
    pub connector_endpoint: Option<String>,
    pub connector_model: Option<String>,
    pub enabled_market_flags: Vec<String>,
}

impl Default for TerminalConfig {
    fn default() -> Self {
        Self {
            central_standards_url: "https://ultraverbaluxmentis.org/sophia/api".to_string(),
            local_llm_url: Some("http://localhost:11434".to_string()),
            connector_type: "LocalLLMConnector".to_string(),
            connector_endpoint: Some("http://localhost:11434".to_string()),
            connector_model: Some("llama3.1".to_string()),
            enabled_market_flags: vec!["enterprise_workflows".to_string()],
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectorEnvelope {
    pub connector_type: String,
    pub endpoint_host: Option<String>,
    pub model: Option<String>,
    pub status: String,
    pub timestamp_utc: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectorTestResult {
    pub ok: bool,
    pub detail: String,
    pub latency_ms: u128,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CentralSyncState {
    pub status: String,
    pub detail: String,
    pub manifest_hash: Option<String>,
    pub updated_at_utc: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Axiom9Guardrails {
    pub forbidden_need_markets: Vec<String>,
    pub allowed_want_markets: Vec<String>,
}

pub fn config_path(base: Option<PathBuf>) -> PathBuf {
    let base_dir = base.or_else(home_dir).unwrap_or_else(|| PathBuf::from("."));
    base_dir.join(".sophia").join("config.json")
}

pub fn connector_tel_path(base: Option<PathBuf>) -> PathBuf {
    let base_dir = base.or_else(home_dir).unwrap_or_else(|| PathBuf::from("."));
    base_dir.join(".sophia").join("connector_tel.jsonl")
}

pub fn central_sync_path(base: Option<PathBuf>) -> PathBuf {
    let base_dir = base.or_else(home_dir).unwrap_or_else(|| PathBuf::from("."));
    base_dir.join(".sophia").join("central_sync.json")
}

pub fn guardrails_path(repo_root: &PathBuf) -> PathBuf {
    repo_root.join("config").join("axiom9_guardrails.json")
}

pub fn load_config(base: Option<PathBuf>) -> TerminalConfig {
    let path = config_path(base);
    if let Ok(contents) = fs::read_to_string(path) {
        if let Ok(config) = serde_json::from_str::<TerminalConfig>(&contents) {
            return config;
        }
    }
    TerminalConfig::default()
}

pub fn save_config(base: Option<PathBuf>, config: &TerminalConfig) -> Result<(), String> {
    let path = config_path(base);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|err| err.to_string())?;
    }
    let payload = serde_json::to_string_pretty(config).map_err(|err| err.to_string())?;
    fs::write(path, payload).map_err(|err| err.to_string())
}

pub fn append_connector_event(base: Option<PathBuf>, envelope: &ConnectorEnvelope) -> Result<(), String> {
    let path = connector_tel_path(base);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|err| err.to_string())?;
    }
    let mut line = serde_json::to_string(envelope).map_err(|err| err.to_string())?;
    line.push('\n');
    use std::io::Write;
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .map_err(|err| err.to_string())?;
    file.write_all(line.as_bytes()).map_err(|err| err.to_string())
}

pub fn write_central_sync_state(base: Option<PathBuf>, sync: &CentralSyncState) -> Result<(), String> {
    let path = central_sync_path(base);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|err| err.to_string())?;
    }
    let payload = serde_json::to_string_pretty(sync).map_err(|err| err.to_string())?;
    fs::write(path, payload).map_err(|err| err.to_string())
}

pub fn find_free_port(start: u16, attempts: u16) -> Result<u16, String> {
    for offset in 0..attempts {
        let port = start + offset;
        if TcpListener::bind(("127.0.0.1", port)).is_ok() {
            return Ok(port);
        }
    }
    Err("No free port found".to_string())
}

pub fn spawn_gateway(port: u16, repo_root: &PathBuf) -> Result<Child, String> {
    Command::new("python")
        .args([
            "-m",
            "uvicorn",
            "tools.sophia.standards_api:app",
            "--port",
            &port.to_string(),
        ])
        .current_dir(repo_root)
        .spawn()
        .map_err(|err| err.to_string())
}

pub fn test_connector_endpoint(endpoint: &str) -> ConnectorTestResult {
    let start = Instant::now();
    let parsed = match Url::parse(endpoint) {
        Ok(url) => url,
        Err(err) => {
            return ConnectorTestResult {
                ok: false,
                detail: format!("invalid_endpoint: {err}"),
                latency_ms: 0,
            }
        }
    };
    let host = match parsed.host_str() {
        Some(host) => host.to_string(),
        None => {
            return ConnectorTestResult {
                ok: false,
                detail: "missing_host".to_string(),
                latency_ms: 0,
            }
        }
    };
    let port = parsed.port_or_known_default().unwrap_or(80);
    let addr = format!("{host}:{port}");
    let mut addrs = match addr.to_socket_addrs() {
        Ok(addrs) => addrs,
        Err(err) => {
            return ConnectorTestResult {
                ok: false,
                detail: format!("resolve_failed: {err}"),
                latency_ms: 0,
            }
        }
    };
    let socket = match addrs.next() {
        Some(sock) => sock,
        None => {
            return ConnectorTestResult {
                ok: false,
                detail: "resolve_failed: no_address".to_string(),
                latency_ms: 0,
            }
        }
    };

    let timeout = Duration::from_secs(3);
    match TcpStream::connect_timeout(&socket, timeout) {
        Ok(_) => ConnectorTestResult {
            ok: true,
            detail: format!("connected:{host}:{port}"),
            latency_ms: start.elapsed().as_millis(),
        },
        Err(err) => ConnectorTestResult {
            ok: false,
            detail: format!("connect_failed: {err}"),
            latency_ms: start.elapsed().as_millis(),
        },
    }
}

#[derive(Debug, Deserialize)]
struct WellKnown {
    manifest_url: String,
}

#[derive(Debug, Deserialize)]
struct ManifestEntry {
    sha256: Option<String>,
}

#[derive(Debug, Deserialize)]
struct Manifest {
    schemas: Vec<ManifestEntry>,
}

pub fn check_central_sync(url: &str, base: Option<PathBuf>) -> Result<CentralSyncState, String> {
    let client = reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(5))
        .build()
        .map_err(|err| err.to_string())?;

    let base_url = url.trim_end_matches('/');
    let well_known_url = format!("{base_url}/.well-known/sophia.json");
    let wk_resp = client.get(well_known_url).send().map_err(|err| err.to_string())?;
    if !wk_resp.status().is_success() {
        return Ok(CentralSyncState {
            status: "down".to_string(),
            detail: format!("well_known_http_{}", wk_resp.status()),
            manifest_hash: None,
            updated_at_utc: chrono::Utc::now().to_rfc3339(),
        });
    }
    let wk: WellKnown = wk_resp.json().map_err(|err| err.to_string())?;
    let manifest_url = if wk.manifest_url.starts_with("http") {
        wk.manifest_url
    } else {
        format!("{base_url}{}", wk.manifest_url)
    };

    let manifest_resp = client.get(manifest_url).send().map_err(|err| err.to_string())?;
    if !manifest_resp.status().is_success() {
        return Ok(CentralSyncState {
            status: "down".to_string(),
            detail: format!("manifest_http_{}", manifest_resp.status()),
            manifest_hash: None,
            updated_at_utc: chrono::Utc::now().to_rfc3339(),
        });
    }
    let bytes = manifest_resp.bytes().map_err(|err| err.to_string())?;
    let manifest: Manifest = serde_json::from_slice(&bytes).map_err(|err| err.to_string())?;
    let schemas_ok = !manifest.schemas.is_empty()
        && manifest
            .schemas
            .iter()
            .all(|entry| entry.sha256.as_ref().map(|v| !v.is_empty()).unwrap_or(false));
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    let manifest_hash = format!("{:x}", hasher.finalize());

    let state = CentralSyncState {
        status: if schemas_ok { "ok".to_string() } else { "stale".to_string() },
        detail: if schemas_ok {
            "central_manifest_valid".to_string()
        } else {
            "central_manifest_missing_schema_hashes".to_string()
        },
        manifest_hash: Some(manifest_hash),
        updated_at_utc: chrono::Utc::now().to_rfc3339(),
    };
    write_central_sync_state(base, &state)?;
    Ok(state)
}

pub fn validate_market_flags(flags: &[String], guardrails: &Axiom9Guardrails) -> Result<(), String> {
    for forbidden in &guardrails.forbidden_need_markets {
        if flags.iter().any(|item| item == forbidden) {
            return Err(format!("forbidden_need_market_flag: {forbidden}"));
        }
    }
    Ok(())
}

pub fn load_guardrails(path: &PathBuf) -> Result<Axiom9Guardrails, String> {
    let data = fs::read_to_string(path).map_err(|err| err.to_string())?;
    serde_json::from_str::<Axiom9Guardrails>(&data).map_err(|err| err.to_string())
}

pub struct TerminalState {
    pub port: u16,
    pub config: Mutex<TerminalConfig>,
    pub child: Mutex<Option<Child>>,
    pub config_base: Option<PathBuf>,
    pub repo_root: PathBuf,
}

impl TerminalState {
    pub fn stop_child(&self) {
        if let Ok(mut guard) = self.child.lock() {
            if let Some(mut child) = guard.take() {
                let _ = child.kill();
                let _ = child.wait();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_config_roundtrip() {
        let tmp = tempdir().expect("tempdir");
        let base = tmp.path().to_path_buf();
        let config = TerminalConfig::default();
        save_config(Some(base.clone()), &config).expect("save config");
        let loaded = load_config(Some(base));
        assert_eq!(loaded.central_standards_url, config.central_standards_url);
        assert_eq!(loaded.local_llm_url, config.local_llm_url);
        assert_eq!(loaded.connector_type, config.connector_type);
    }

    #[test]
    fn test_find_free_port_skips_used() {
        let listener = TcpListener::bind(("127.0.0.1", 8001)).expect("bind 8001");
        let port = find_free_port(8001, 5).expect("find port");
        assert_eq!(port, 8002);
        drop(listener);
    }

    #[test]
    fn test_connector_tel_write_shape() {
        let tmp = tempdir().expect("tempdir");
        let envelope = ConnectorEnvelope {
            connector_type: "LocalLLMConnector".to_string(),
            endpoint_host: Some("localhost".to_string()),
            model: Some("llama3.1".to_string()),
            status: "ok".to_string(),
            timestamp_utc: chrono::Utc::now().to_rfc3339(),
        };
        append_connector_event(Some(tmp.path().to_path_buf()), &envelope).expect("append");
        let path = connector_tel_path(Some(tmp.path().to_path_buf()));
        let line = fs::read_to_string(path).expect("read");
        let parsed: serde_json::Value = serde_json::from_str(line.trim()).expect("json");
        assert!(parsed.get("connector_type").is_some());
        assert!(parsed.get("status").is_some());
        assert!(parsed.get("timestamp_utc").is_some());
    }

    #[test]
    fn test_central_sync_persistence_roundtrip() {
        let tmp = tempdir().expect("tempdir");
        let state = CentralSyncState {
            status: "ok".to_string(),
            detail: "central_manifest_valid".to_string(),
            manifest_hash: Some("abc123".to_string()),
            updated_at_utc: chrono::Utc::now().to_rfc3339(),
        };
        write_central_sync_state(Some(tmp.path().to_path_buf()), &state).expect("write");
        let path = central_sync_path(Some(tmp.path().to_path_buf()));
        let data: CentralSyncState =
            serde_json::from_str(&fs::read_to_string(path).expect("read")).expect("parse");
        assert_eq!(data.status, "ok");
        assert_eq!(data.manifest_hash, Some("abc123".to_string()));
    }

    #[test]
    fn test_axiom9_forbidden_market_flag_rejected() {
        let guardrails = Axiom9Guardrails {
            forbidden_need_markets: vec!["housing".to_string(), "food".to_string()],
            allowed_want_markets: vec!["enterprise_workflows".to_string()],
        };
        let bad = vec!["housing".to_string()];
        assert!(validate_market_flags(&bad, &guardrails).is_err());
    }
}
