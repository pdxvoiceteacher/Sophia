from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_rupture_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_prefer_rupture_map_and_warn_high_ratio(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "rupture_map.json", {"generatedAt": "2027-01-01T00:00:00Z", "invariantHash": "sha256:r", "targets": [{"phaseId": "r:a", "ruptureRatio": 1.3}]})
    _write(bridge / "rupture_signal_map.json", {"targets": [{"phaseId": "fallback", "ruptureRatio": 0.2}]})
    payload = module.build_outputs(bridge_root=bridge)
    assert payload["decision"] == "warn"
    assert payload["findings"][0]["id"] == "r:a"


def test_top_level_rupture_ratio_shape(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "rupture_map.json", {"generatedAt": "2027-01-01T00:00:00Z", "phaseId": "r:top", "ruptureRatio": 0.5})
    payload = module.build_outputs(bridge_root=bridge)
    assert payload["decision"] == "pass"
    assert payload["findings"][0]["type"] == "within-bounds"


def test_empty_input_fail_closed_single_docket(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "rupture_signal_map.json", {})
    payload = module.build_outputs(bridge_root=bridge)
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["advisory"] == "docket"


def test_schema_rejects_suppress() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/rupture_audit_v1.schema.json").read_text())
    bad = {
        "schema": "rupture_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "warn",
        "findings": [{"id": "x", "severity": "warn", "type": "rupture-risk", "advisory": "suppress", "message": "m", "data": {}}],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad)
