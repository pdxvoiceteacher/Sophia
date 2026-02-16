from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator


ROOT = Path(__file__).resolve().parents[1]


def test_network_policy_schema_validates_seed_config() -> None:
    schema = json.loads((ROOT / "schema" / "network_policy_v1.schema.json").read_text(encoding="utf-8-sig"))
    payload = json.loads((ROOT / "config" / "network_policy_v1.json").read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(payload)
    assert payload["relay_toggles"]["evidence_full_relay"] is False
    assert payload["relay_toggles"]["vault_relay"] is False


def test_peer_registry_seed_contains_policy_and_trust_fields() -> None:
    payload = json.loads((ROOT / "config" / "peer_registry_v1.json").read_text(encoding="utf-8-sig"))
    peers = payload.get("peers") or []
    assert peers, "peer registry must include at least one seed peer"
    first = peers[0]
    assert first.get("trust_tier") in {"witness", "compute", "full_relay"}
    allowed = first.get("allowed_policy_profiles")
    assert isinstance(allowed, list) and all(isinstance(item, str) for item in allowed)




def test_network_policy_share_scope_allowlist_and_relay_terms_documented() -> None:
    schema = json.loads((ROOT / "schema" / "network_policy_v1.schema.json").read_text(encoding="utf-8-sig"))
    allowed = set(schema["properties"]["share_scopes"]["items"]["enum"])
    assert {"hashes/*", "metrics/*", "attestations/*", "tel/*", "evidence/*", "vault/*"}.issubset(allowed)

    policy_doc = (ROOT / "docs" / "P2P_NETWORK_POLICY.md").read_text(encoding="utf-8")
    assert "AI-private by default" in policy_doc
    assert "evidence_full_relay" in policy_doc
    assert "vault_relay" in policy_doc
    assert "Canonical JSON" in policy_doc

def test_tauri_network_policy_commands_registered_and_response_shape_present() -> None:
    main_rs = (ROOT / "desktop" / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert "fn get_network_policy(" in main_rs
    assert "fn save_network_policy(" in main_rs
    assert "get_network_policy," in main_rs
    assert "save_network_policy," in main_rs

    assert "network_required: bool" in main_rs
    assert "degraded_mode: bool" in main_rs
    assert "network_required," in main_rs
    assert "degraded_mode," in main_rs


def test_validate_attestation_file_uses_run_python_without_env() -> None:
    main_rs = (ROOT / "desktop" / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    start = main_rs.index("fn validate_attestation_file(")
    end = main_rs.index("fn summarize_attestations(")
    block = main_rs[start:end]
    assert "run_python(" in block
    assert "run_python_with_env(" not in block


def test_peer_attestation_demo_signature_is_marked_placeholder() -> None:
    main_rs = (ROOT / "desktop" / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert "demo-ed25519-placeholder" in main_rs
    assert "demo-sig:" in main_rs
    assert "signed_bytes_hash" in main_rs
    assert "canonical JSON" in main_rs
    assert "TODO(crypto): replace demo signature scaffold" in main_rs


def test_request_peer_attestation_attaches_peer_attestations_to_epoch_manifest() -> None:
    main_rs = (ROOT / "desktop" / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert 'run_dir.join("peer_attestations.json")' in main_rs
    assert '"peer_attestations.json".to_string()' in main_rs
    assert 'get_mut("outputs_manifest")' in main_rs


def test_save_network_policy_enforces_scope_and_profile_constraints() -> None:
    main_rs = (ROOT / "desktop" / "src-tauri" / "src" / "main.rs").read_text(encoding="utf-8")
    assert "invalid_share_scope" in main_rs
    assert "witness_only_disallows_vault_and_evidence_scopes" in main_rs
    assert "reproducible_audit_disallows_vault_scope" in main_rs
    assert "vault_scope_requires_full_relay_profile" in main_rs
