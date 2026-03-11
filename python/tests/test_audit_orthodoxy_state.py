from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_orthodoxy_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_warn_and_watch_docket_only(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(
        b / "orthodoxy_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {"targetId": "a", "orthodoxyScore": 0.8, "orthodoxyAlert": False},
                {"targetId": "b", "orthodoxyScore": 0.3, "orthodoxyAlert": False},
            ],
        },
    )
    _write(s / "orthodoxy_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/orthodoxy_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "ORTHODOXY_MAP_PATH", b / "orthodoxy_map.json")
    monkeypatch.setattr(module, "ORTHODOXY_AUDIT_SCHEMA_PATH", s / "orthodoxy_audit_v1.schema.json")

    payload = module.build_outputs()
    assert payload["decision"] == "warn"
    assert any(f["type"] == "orthodoxy-risk" for f in payload["findings"])
    assert all(f["advisory"] in {"watch", "docket"} for f in payload["findings"])

    text = " ".join(f["message"] for f in payload["findings"]).lower()
    assert "coerced coherence" in text
    Draft202012Validator(json.loads((s / "orthodoxy_audit_v1.schema.json").read_text())).validate(payload)


def test_missing_fields_fail_closed_docket(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "orthodoxy_map.json", {"targets": [{"targetId": "x"}]})
    _write(s / "orthodoxy_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/orthodoxy_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "ORTHODOXY_MAP_PATH", b / "orthodoxy_map.json")
    monkeypatch.setattr(module, "ORTHODOXY_AUDIT_SCHEMA_PATH", s / "orthodoxy_audit_v1.schema.json")

    payload = module.build_outputs()
    finding = payload["findings"][0]
    assert finding["type"] == "missing-fields"
    assert finding["advisory"] == "docket"
