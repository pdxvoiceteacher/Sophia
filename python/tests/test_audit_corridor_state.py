from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_corridor_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_corridor_emerging_info(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(
        b / "corridor_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {"targetId": "a", "corridorPotential": 0.81},
                {"targetId": "b", "corridorPotential": 0.41},
            ],
        },
    )
    _write(s / "corridor_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/corridor_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "CORRIDOR_MAP_PATH", b / "corridor_map.json")
    monkeypatch.setattr(module, "CORRIDOR_AUDIT_SCHEMA_PATH", s / "corridor_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "pass"
    assert any(f["type"] == "corridor-emerging" for f in payload["findings"])
    assert all(f["severity"] in {"warn", "info"} for f in payload["findings"])
    assert all(f["advisory"] in {"watch", "docket"} for f in payload["findings"])

    text = " ".join(f["message"] for f in payload["findings"]).lower()
    assert "possible new discovery corridor forming" in text
    Draft202012Validator(json.loads((s / "corridor_audit_v1.schema.json").read_text())).validate(payload)


def test_missing_fields_fail_closed_docket(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "corridor_map.json", {"targets": [{"targetId": "x"}]})
    _write(s / "corridor_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/corridor_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "CORRIDOR_MAP_PATH", b / "corridor_map.json")
    monkeypatch.setattr(module, "CORRIDOR_AUDIT_SCHEMA_PATH", s / "corridor_audit_v1.schema.json")

    payload = module.build_outputs()
    finding = payload["findings"][0]
    assert finding["type"] == "missing-fields"
    assert finding["advisory"] == "docket"
