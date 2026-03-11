from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_rebraid_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_high_rebraid_potential_emits_advisory(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(
        b / "rebraid_signal_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {"targetId": "braid:a", "rebraidPotential": 0.82, "rebraidAlert": True},
                {"targetId": "braid:b", "rebraidPotential": 0.40, "rebraidAlert": False},
            ],
        },
    )
    _write(s / "rebraid_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/rebraid_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "REBRAID_SIGNAL_MAP_PATH", b / "rebraid_signal_map.json")
    monkeypatch.setattr(module, "REBRAID_AUDIT_SCHEMA_PATH", s / "rebraid_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "pass"
    assert any(f["type"] == "rebraiding-emerging" for f in payload["findings"])
    assert all(f["advisory"] in {"watch", "docket"} for f in payload["findings"])
    Draft202012Validator(json.loads((s / "rebraid_audit_v1.schema.json").read_text())).validate(payload)


def test_schema_rejects_disallowed_action() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/rebraid_audit_v1.schema.json").read_text())
    bad = {
        "schema": "rebraid_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "pass",
        "findings": [
            {
                "id": "x",
                "severity": "info",
                "type": "rebraiding-emerging",
                "message": "msg",
                "advisory": "merge",
                "data": {"rebraidPotential": 0.8},
            }
        ],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad)


def test_empty_input_fail_closed_docket(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "rebraid_signal_map.json", {})
    _write(s / "rebraid_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/rebraid_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "REBRAID_SIGNAL_MAP_PATH", b / "rebraid_signal_map.json")
    monkeypatch.setattr(module, "REBRAID_AUDIT_SCHEMA_PATH", s / "rebraid_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["type"] == "docket-review"
    assert payload["findings"][0]["advisory"] == "docket"
