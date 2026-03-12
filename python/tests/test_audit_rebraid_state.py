from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_rebraid_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_rebraid_audit_missing_input_fail_closed() -> None:
    payload = module.build_outputs(bridge_root=Path("/tmp/no-rebraid-input"))
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["advisory"] == "docket"
    assert payload["findings"][0]["type"] == "rebraid"


def test_rebraid_audit_strength_high_warn(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "rebraid_signal_map.json", {"generatedAt": "2027-01-01T00:00:00Z", "rebraidStrength": 0.8})
    payload = module.build_outputs(bridge_root=bridge)
    assert payload["findings"][0]["advisory"] == "watch"
    assert payload["findings"][0]["severity"] == "warn"
    assert "strong" in payload["findings"][0]["message"].lower()


def test_schema_rejects_invalid_advisory() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/rebraid_audit_v1.schema.json").read_text())
    bad_payload = {
        "schema": "rebraid_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "pass",
        "findings": [
            {
                "id": "x",
                "severity": "info",
                "type": "rebraid",
                "advisory": "merge",
                "message": "bad",
                "data": {},
            }
        ],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad_payload)


def test_compat_entrypoint_writes_file(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "rebraid_signal_map.json", {"generatedAt": "2027-01-01T00:00:00Z", "rebraidStrength": 0.8})
    out = tmp_path / "rebraid_audit.json"

    module.audit_rebraid_state(str(bridge), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["findings"][0]["advisory"] in {"watch", "docket"}
