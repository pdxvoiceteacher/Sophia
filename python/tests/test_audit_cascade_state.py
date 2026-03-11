from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_cascade_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_health_low_warns(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    schema = tmp_path / "schema/cascade_audit_v1.schema.json"
    _write(bridge / "coherence_cascade_map.json", {"generatedAt": "2027-01-01T00:00:00Z", "coherenceCascadeMap": {"cascadeHealth": 0.42}})
    _write(schema, json.loads(Path("/workspace/Sophia/schema/cascade_audit_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "SCHEMA_PATH", schema)
    payload = module.build_outputs(bridge_root=bridge)
    assert payload["decision"] == "warn"
    assert payload["findings"][0]["id"] == "cascade.healthLow"
    assert payload["findings"][0]["advisory"] in {"watch", "docket"}
    Draft202012Validator(json.loads(schema.read_text())).validate(payload)


def test_missing_input_fail_closed() -> None:
    payload = module.build_outputs(bridge_root=Path("/tmp/does-not-exist-cascade"))
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["advisory"] == "docket"


def test_schema_rejects_disallowed_advisory() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/cascade_audit_v1.schema.json").read_text())
    bad_payload = {
        "schema": "cascade_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "warn",
        "findings": [
            {
                "id": "cascade.bad",
                "severity": "warn",
                "type": "audit",
                "advisory": "merge",
                "message": "bad",
                "data": {},
            }
        ],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad_payload)
