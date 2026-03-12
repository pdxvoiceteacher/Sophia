from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_civilizational_delta_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_direct_delta_map_ingestion(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(
        bridge / "civilizational_delta_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "invariantHash": "sha256:d",
            "targets": [
                {"phaseId": "delta:a", "deltaStrength": 12.0, "deltaAlert": False},
                {"phaseId": "delta:b", "deltaStrength": 3.0, "deltaAlert": False},
            ],
        },
    )

    payload = module.build_outputs(bridge_root=bridge)
    assert payload["decision"] == "warn"
    assert any(f["type"] == "delta-risk" for f in payload["findings"])
    assert all(f["advisory"] in {"watch", "docket"} for f in payload["findings"])


def test_missing_delta_map_fail_closed(tmp_path: Path) -> None:
    payload = module.build_outputs(bridge_root=tmp_path / "missing")
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["advisory"] == "docket"


def test_schema_rejects_merge_action() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/civilizational_delta_audit_v1.schema.json").read_text())
    bad = {
        "schema": "civilizational_delta_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "pass",
        "findings": [{"id": "x", "severity": "info", "type": "within-bounds", "advisory": "merge", "message": "m", "data": {}}],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad)


def test_compat_entrypoint_writes_file(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "civilizational_delta_map.json", {"generatedAt": "2027-01-01T00:00:00Z", "targets": [{"phaseId": "d:1", "deltaStrength": 2.0}]})
    out = tmp_path / "delta_audit.json"

    module.audit_civilizational_delta_state(str(tmp_path), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["findings"][0]["advisory"] in {"watch", "docket"}
