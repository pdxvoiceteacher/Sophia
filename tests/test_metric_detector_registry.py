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
