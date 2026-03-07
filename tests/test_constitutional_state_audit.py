from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_constitutional_state

REPO = Path(__file__).resolve().parents[1]


def test_constitutional_outputs_validate_and_are_sorted() -> None:
    rc = audit_constitutional_state.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "constitutional_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "constitutional_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "constitutional_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "constitutional_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row.get("principleId", row.get("systemTargetId", "")) for row in audit_payload["evaluations"]]
    assert ids == sorted(ids)

    first = recommendations_payload["recommendations"][0]
    assert first["constitutionalStatus"] in {"aligned", "strained", "violated", "indeterminate"}
    assert first["recommendedAction"] in {
        "continue",
        "increase-watch",
        "freeze-promotions",
        "freeze-governance-intake",
        "preservation-mode",
        "require-human-emergency-review",
    }


def test_constitutional_cautions_stay_bounded() -> None:
    audit_payload = json.loads((REPO / "bridge" / "constitutional_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "constitutional_recommendations.json").read_text(encoding="utf-8"))

    caution1 = audit_payload.get("caution", "").lower()
    caution2 = recommendations_payload.get("caution", "").lower()

    assert "constraints" in caution1
    assert "no unconstrained self-governance" in caution1
    assert "freeze-and-preserve" in caution2
    assert "not self-sovereign expansion" in caution2
