from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DESKTOP = ROOT / "desktop"


def test_desktop_layout_exists() -> None:
    required = [
        DESKTOP / "package.json",
        DESKTOP / "src" / "index.html",
        DESKTOP / "src" / "main.js",
        DESKTOP / "src" / "style.css",
        DESKTOP / "src-tauri" / "Cargo.toml",
        DESKTOP / "src-tauri" / "tauri.conf.json",
        DESKTOP / "src-tauri" / "src" / "main.rs",
        DESKTOP / "src-tauri" / "src" / "state.rs",
    ]
    missing = [path for path in required if not path.exists()]
    assert not missing, f"Missing desktop files: {missing}"


def test_terminal_connector_controls_present() -> None:
    html = (DESKTOP / "src" / "index.html").read_text(encoding="utf-8")
    for element_id in [
        "connector-type",
        "connector-endpoint",
        "connector-model",
        "add-connector",
        "active-connector",
        "connector-list",
        "test-connector",
        "ucc-status",
        "check-central-sync",
        "run-epoch-test",
        "epoch-status",
        "epoch-summary",
        "epoch-sentinel",
        "review-attestation-path",
        "review-submission-id",
        "review-status",
        "fetch-attestations",
        "submit-cross-review",
        "create-local-bundle",
        "review-central-url",
        "review-attestation-summary",
        "epoch-experimental-scenario",
        "epoch-baseline-scenario",
    ]:
        assert f'id="{element_id}"' in html


def test_windows_operator_scripts_exist() -> None:
    for path in [
        ROOT / "scripts" / "windows" / "dev.ps1",
        ROOT / "scripts" / "windows" / "dev_up.ps1",
        ROOT / "scripts" / "windows" / "doctor.ps1",
    ]:
        assert path.exists(), f"Missing script: {path}"


def test_tauri_command_names_wired() -> None:
    main_rs = (DESKTOP / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    for symbol in [
        "fn test_connector_endpoint(",
        "fn check_central_sync(",
        "fn validate_enabled_market_flags(",
        "test_connector_endpoint,",
        "check_central_sync",
        "validate_enabled_market_flags",
        "fn run_epoch_test(",
        "fn log_epoch_event(",
        "run_epoch_test",
        "log_epoch_event",
        "fetch_attestations",
        "create_cross_review_submission",
        "list_epoch_scenarios",
        "fn fetch_attestations(",
        "fn create_cross_review_submission(",
        "fn list_epoch_scenarios(",
        "fn get_active_connector_config(",
        "get_active_connector_config",
    ]:
        assert symbol in main_rs


def test_axiom9_guardrails_json_valid() -> None:
    path = ROOT / "config" / "axiom9_guardrails.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    assert payload["forbidden_need_markets"]
    assert payload["allowed_want_markets"]


def test_tauri_sentinel_fallback_logic_present() -> None:
    main_rs = (DESKTOP / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert "sentinel_state.json" in main_rs
    assert "serde_json::from_str" in main_rs
    assert '\\"state\\":\\"normal\\"' in main_rs
    assert "unwrap_or_else(|_|" in main_rs
    assert "json!({" in main_rs
    assert "\"state\": \"normal\"" in main_rs
    assert "\"reasons\": []" in main_rs


def test_tauri_main_has_no_duplicate_unwrap_or_default_lines() -> None:
    main_rs = (DESKTOP / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert ".unwrap_or_default();\n        .unwrap_or_default();" not in main_rs


def test_attestations_attach_to_run_wired() -> None:
    main_js = (DESKTOP / "src" / "main.js").read_text(encoding="utf-8")
    main_rs = (DESKTOP / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert "runFolder: state.lastEpochResult?.run_folder || null" in main_js
    assert "run_folder: Option<String>" in main_rs
    assert "run_dir.join(\"attestations.json\")" in main_rs


def test_submit_cross_review_has_single_runfolder_key() -> None:
    main_js = (DESKTOP / "src" / "main.js").read_text(encoding="utf-8")
    submit_block = main_js.split("async function submitCrossReview()", 1)[1].split("async function createLocalBundle()", 1)[0]
    assert submit_block.count("runFolder:") == 1
