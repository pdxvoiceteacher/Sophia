from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_rupture_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_rupture_audit_triggers_warning(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(
        b / "rupture_signal_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {"phaseId": "R1", "ruptureRatio": 1.2},
                {"phaseId": "R2", "ruptureRatio": 0.5}
            ],
        },
    )
    _write(s / "rupture_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/rupture_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "RUPTURE_SIGNAL_MAP_PATH", b / "rupture_signal_map.json")
    monkeypatch.setattr(module, "RUPTURE_AUDIT_SCHEMA_PATH", s / "rupture_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "warn"
    assert any(f["type"] == "rupture-risk" and f["severity"] == "warn" for f in payload["findings"])
    assert all(f["advisory"] in {"watch", "docket"} for f in payload["findings"])
    Draft202012Validator(json.loads((s / "rupture_audit_v1.schema.json").read_text())).validate(payload)


def test_schema_rejects_disallowed_advisory() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/rupture_audit_v1.schema.json").read_text())
    bad = {
        "schema": "rupture_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "warn",
        "findings": [
            {
                "id": "R1",
                "severity": "warn",
                "type": "rupture-risk",
                "advisory": "suppress",
                "message": "msg",
                "data": {"ruptureRatio": 1.2}
            }
        ],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad)


def test_missing_input_generates_single_docket(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "rupture_signal_map.json", {})
    _write(s / "rupture_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/rupture_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "RUPTURE_SIGNAL_MAP_PATH", b / "rupture_signal_map.json")
    monkeypatch.setattr(module, "RUPTURE_AUDIT_SCHEMA_PATH", s / "rupture_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["type"] == "docket-review"
    assert payload["findings"][0]["advisory"] == "docket"
