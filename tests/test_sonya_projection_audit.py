from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_sonya_projection

REPO = Path(__file__).resolve().parents[1]


def test_audit_projection_writes_schema_valid_ordered_outputs() -> None:
    rc = audit_sonya_projection.main()
    assert rc == 0

    audit_path = REPO / "bridge" / "sonya_audit.json"
    decisions_path = REPO / "bridge" / "sonya_admission_decisions.json"
    assert audit_path.exists()
    assert decisions_path.exists()

    audit_payload = json.loads(audit_path.read_text(encoding="utf-8"))
    decisions_payload = json.loads(decisions_path.read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "sonya_audit_v1.schema.json").read_text(encoding="utf-8"))
    decisions_schema = json.loads((REPO / "schema" / "sonya_admission_decisions_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(decisions_schema).validate(decisions_payload)

    input_ids = [d["inputId"] for d in decisions_payload["decisions"]]
    assert input_ids == sorted(input_ids)

    first = decisions_payload["decisions"][0]
    assert "governingRule" in first
    assert "explanation" in first and first["explanation"]
    assert first["targetPublisherAction"] in {"store", "annotate", "hold", "discard"}


def test_audit_includes_phaselock_contract_text() -> None:
    payload = json.loads((REPO / "bridge" / "sonya_audit.json").read_text(encoding="utf-8"))
    assert "raw Sonya input -> CoherenceLattice projection -> Sophia audit -> Publisher memory storage" in payload["phaselock"]
