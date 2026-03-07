from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_precedent_state

REPO = Path(__file__).resolve().parents[1]


def test_precedent_outputs_validate_and_are_sorted() -> None:
    rc = audit_precedent_state.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "precedent_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "precedent_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "precedent_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "precedent_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    case_ids = [row["caseId"] for row in audit_payload["records"]]
    assert case_ids == sorted(case_ids)

    first = recommendations_payload["recommendations"][0]
    assert first["precedentStatus"] in {
        "follow-precedent",
        "distinguish-case",
        "watch-divergence",
        "reject-analogy",
        "require-broader-human-review",
    }
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_precedent_caution_is_advisory_and_non_binding() -> None:
    audit_payload = json.loads((REPO / "bridge" / "precedent_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "precedent_recommendations.json").read_text(encoding="utf-8"))

    c1 = audit_payload.get("caution", "").lower()
    c2 = recommendations_payload.get("caution", "").lower()
    assert "advisory" in c1
    assert "persuasive" in c1
    assert "divergence may be legitimate" in c2
    assert "no automatic doctrine hardening" in c2
