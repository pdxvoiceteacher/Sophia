from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_governance_candidates

REPO = Path(__file__).resolve().parents[1]


def test_governance_outputs_validate_and_are_sorted() -> None:
    rc = audit_governance_candidates.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "governance_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "governance_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "governance_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "governance_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    reviewer_ids = [row["reviewerId"] for row in audit_payload["audits"]]
    assert reviewer_ids == sorted(reviewer_ids)

    first = recommendations_payload["recommendations"][0]
    assert first["governanceStatus"] in {"eligible", "watch", "hold", "recommend-human-review", "ineligible"}
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_governance_caution_is_advisory_non_automatic() -> None:
    recommendations_payload = json.loads((REPO / "bridge" / "governance_recommendations.json").read_text(encoding="utf-8"))
    caution = recommendations_payload.get("caution", "").lower()
    assert "advisory" in caution
    assert "human/community" in caution
