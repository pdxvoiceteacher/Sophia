from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_institutional_state

REPO = Path(__file__).resolve().parents[1]


EXPECTED_STATUSES = {
    "stable",
    "monitor",
    "caution",
    "freeze-pathways",
    "require-human-review",
    "preservation-mode",
}


def test_institutional_outputs_validate_and_are_sorted() -> None:
    rc = audit_institutional_state.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "institutional_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "institutional_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "institutional_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads(
        (REPO / "schema" / "institutional_recommendations_v1.schema.json").read_text(encoding="utf-8")
    )

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row["institutionId"] for row in audit_payload["records"]]
    assert ids == sorted(ids)

    statuses = {row["institutionalStatus"] for row in recommendations_payload["recommendations"]}
    assert statuses == EXPECTED_STATUSES


def test_institutional_outputs_are_bounded_and_non_mutating() -> None:
    audit_payload = json.loads((REPO / "bridge" / "institutional_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "institutional_recommendations.json").read_text(encoding="utf-8"))

    assert "bounded" in audit_payload.get("caution", "").lower()
    assert "does not mutate canonical truth" in audit_payload.get("caution", "").lower()
    assert "without mutating canonical truth" in recommendations_payload.get("phaselock", "").lower()
    assert "bounded advisory" in recommendations_payload.get("caution", "").lower()
