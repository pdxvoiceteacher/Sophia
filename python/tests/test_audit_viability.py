from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, ValidationError

from sophia import audit_cascade_viability as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_viability_warns_below_threshold(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(
        bridge / "coherence_cascade_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "coherencePsi": 0.5,
            "plurality": 0.5,
            "trustLegibility": 0.5,
            "memoryScore": 0.5,
            "anomalyGradient": 0.5,
            "entropyDrift": 1.0,
            "capturePressure": 0.1,
        },
    )

    out_file = tmp_path / "viability_audit.json"
    module.audit_cascade_viability(str(bridge), str(out_file))
    result = json.loads(out_file.read_text(encoding="utf-8"))

    assert len(result["findings"]) == 1
    finding = result["findings"][0]
    assert finding["severity"] == "warn"
    assert finding["advisory"] == "watch"
    assert finding["type"] == "viability-alert"

    schema = json.loads(Path("/workspace/Sophia/schema/sophia/viability_audit_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(result)


def test_viability_fail_closed_missing_input(tmp_path: Path) -> None:
    payload = module.build_outputs(bridge_root=tmp_path / "missing")
    assert payload["decision"] == "warn"
    assert payload["findings"][0]["advisory"] == "docket"


def test_schema_rejects_disallowed_advisory() -> None:
    schema = json.loads(Path("/workspace/Sophia/schema/sophia/viability_audit_v1.schema.json").read_text(encoding="utf-8"))
    bad_payload = {
        "schema": "viability_audit_v1",
        "created_at": "2027-01-01T00:00:00Z",
        "caution": "bounded",
        "decision": "warn",
        "findings": [
            {
                "id": "viability.bad",
                "severity": "warn",
                "type": "viability-alert",
                "advisory": "merge",
                "message": "bad",
                "data": {},
            }
        ],
    }
    with pytest.raises(ValidationError):
        Draft202012Validator(schema).validate(bad_payload)
