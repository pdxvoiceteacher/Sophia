from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_schism_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_warn_when_alert_or_high_potential(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(
        b / "schism_signal_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {"targetId": "t:1", "schismPotential": 0.8, "sharedPlurality": 0.41, "schismAlert": True},
                {"targetId": "t:2", "schismPotential": 0.3, "sharedPlurality": 0.77, "schismAlert": False},
            ],
        },
    )
    _write(s / "schism_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/schism_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "SCHISM_SIGNAL_MAP_PATH", b / "schism_signal_map.json")
    monkeypatch.setattr(module, "SCHISM_AUDIT_SCHEMA_PATH", s / "schism_audit_v1.schema.json")

    payload = module.build_outputs()

    assert payload["decision"] == "warn"
    assert any(f["type"] == "schism-risk" and f["severity"] == "warn" for f in payload["findings"])
    assert all(f["advisory"] in {"watch", "docket"} for f in payload["findings"])

    Draft202012Validator(json.loads((s / "schism_audit_v1.schema.json").read_text())).validate(payload)


def test_schema_catches_misuse_of_advisory() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/schism_audit_v1.schema.json").read_text())
    bad_payload = {
        "schema": "schism_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "warn",
        "findings": [
            {
                "id": "x",
                "severity": "warn",
                "type": "schism-risk",
                "message": "msg",
                "advisory": "suppress branch",
                "data": {},
            }
        ],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad_payload)


def test_missing_or_empty_targets_fail_closed(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "schism_signal_map.json", {"targets": []})
    _write(s / "schism_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/schism_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "SCHISM_SIGNAL_MAP_PATH", b / "schism_signal_map.json")
    monkeypatch.setattr(module, "SCHISM_AUDIT_SCHEMA_PATH", s / "schism_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "warn"
    assert payload["findings"][0]["advisory"] == "docket"
    assert payload["findings"][0]["type"] == "missing-data"
