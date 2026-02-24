from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator


def test_metric_registry_schema_valid() -> None:
    root = Path(__file__).resolve().parents[1]
    schema = json.loads((root / "schema" / "metric_registry_v1.schema.json").read_text(encoding="utf-8-sig"))
    payload = json.loads((root / "config" / "metric_registry_v1.json").read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(payload)


def test_detector_registry_schema_valid() -> None:
    root = Path(__file__).resolve().parents[1]
    schema = json.loads((root / "schema" / "detector_registry_v1.schema.json").read_text(encoding="utf-8-sig"))
    payload = json.loads((root / "config" / "detector_registry_v1.json").read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(payload)


def test_epoch_analyze_declares_detectors_used() -> None:
    source = (Path(__file__).resolve().parents[1] / "tools" / "telemetry" / "epoch_analyze.py").read_text(encoding="utf-8")
    assert "detectors_used" in source



def test_sentinel_state_schema_accepts_sample() -> None:
    root = Path(__file__).resolve().parents[1]
    schema = json.loads((root / "schema" / "sentinel_state_v1.schema.json").read_text(encoding="utf-8-sig"))
    payload = {
        "schema": "sentinel_state_v1",
        "state": "observe",
        "reasons": ["example detector signal"],
        "artifact_links": ["epoch_findings.json"],
        "policy_profile": "safeguard",
    }
    Draft202012Validator(schema).validate(payload)


def test_sensitive_action_registry_present() -> None:
    root = Path(__file__).resolve().parents[1]
    payload = json.loads((root / "config" / "sensitive_action_registry_v1.json").read_text(encoding="utf-8-sig"))
    assert payload["schema"] == "sensitive_action_registry_v1"
    assert payload["sensitive_tokens"]


def test_action_registry_v2_present() -> None:
    root = Path(__file__).resolve().parents[1]
    payload = json.loads((root / "governance" / "policies" / "action_registry_v2.json").read_text(encoding="utf-8-sig"))
    assert payload["schema"] == "action_registry_v2"
    assert payload["actions"]


def test_audit_prefers_action_registry_v2_classification() -> None:
    source = (Path(__file__).resolve().parents[1] / "tools" / "telemetry" / "sophia_audit.py").read_text(encoding="utf-8")
    assert "load_action_registry_v2" in source
    assert "classify_action" in source
    assert "enforce_action_requirements_by_class" in source
