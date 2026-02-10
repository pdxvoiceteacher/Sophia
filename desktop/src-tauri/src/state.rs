use serde::{Deserialize, Serialize};
use std::fs;
use std::net::TcpListener;
use std::path::PathBuf;
use std::process::{Child, Command};
use std::sync::Mutex;
use tauri::api::path::home_dir;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TerminalConfig {
    pub central_standards_url: String,
    pub local_llm_url: Option<String>,
    pub connector_type: String,
    pub connector_endpoint: Option<String>,
    pub connector_model: Option<String>,
}

impl Default for TerminalConfig {
    fn default() -> Self {
        Self {
            central_standards_url: "https://ultraverbaluxmentis.org/sophia/api".to_string(),
            local_llm_url: Some("http://localhost:11434".to_string()),
            connector_type: "LocalLLMConnector".to_string(),
            connector_endpoint: Some("http://localhost:11434".to_string()),
            connector_model: Some("llama3.1".to_string()),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectorEnvelope {
    pub connector_type: String,
    pub endpoint: Option<String>,
    pub model: Option<String>,
    pub status: String,
    pub timestamp_utc: String,
}

pub fn config_path(base: Option<PathBuf>) -> PathBuf {
    let base_dir = base
        .or_else(home_dir)
        .unwrap_or_else(|| PathBuf::from("."));
    base_dir.join(".sophia").join("config.json")
}

pub fn connector_tel_path(base: Option<PathBuf>) -> PathBuf {
    let base_dir = base
        .or_else(home_dir)
        .unwrap_or_else(|| PathBuf::from("."));
    base_dir.join(".sophia").join("connector_tel.jsonl")
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

pub struct TerminalState {
    pub port: u16,
    pub config: Mutex<TerminalConfig>,
    pub child: Mutex<Option<Child>>,
    pub config_base: Option<PathBuf>,
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
}
