from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_knowledge_river_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_direct_coherencelattice_shape(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(
        bridge / "knowledge_river_map.json",
        {"generatedAt": "2027-01-01T00:00:00Z", "invariantHash": "sha256:a", "rivers": [{"id": "river:a", "riverStrength": 4.5}]},
    )
    _write(bridge / "river_capture_risk_report.json", {"generatedAt": "2027-01-01T00:00:00Z", "rivers": [{"id": "river:a", "captureRisk": 0.7}]})

    payload = module.build_outputs(bridge_root=bridge)
    assert payload["decision"] == "warn"
    assert payload["findings"][0]["type"] == "capture-risk"
    assert payload["findings"][0]["advisory"] in {"watch", "docket"}


def test_fail_closed_on_missing_inputs(tmp_path: Path) -> None:
    payload = module.build_outputs(bridge_root=tmp_path / "missing")
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["advisory"] == "docket"


def test_schema_rejects_disallowed_advisory() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/knowledge_river_audit_v1.schema.json").read_text())
    bad = {
        "schema": "knowledge_river_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "pass",
        "findings": [{"id": "x", "severity": "info", "type": "within-bounds", "advisory": "suppress", "message": "m", "data": {}}],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad)
