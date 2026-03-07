from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_promotion_candidates

REPO = Path(__file__).resolve().parents[1]


def test_promotion_audit_outputs_validate_and_are_sorted() -> None:
    rc = audit_promotion_candidates.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "promotion_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "promotion_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "promotion_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "promotion_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    candidate_ids = [item["candidateId"] for item in audit_payload["audits"]]
    assert candidate_ids == sorted(candidate_ids)

    first = recommendations_payload["recommendations"][0]
    assert first["auditStatus"] in {"recommend-human-review", "hold", "watch", "reject"}
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_promotion_outputs_are_cautious_human_review_only() -> None:
    recommendations_payload = json.loads((REPO / "bridge" / "promotion_recommendations.json").read_text(encoding="utf-8"))
    caution = recommendations_payload.get("caution", "").lower()
    assert "human review" in caution
    assert "canonical truth" in caution
    assert all(item["auditStatus"] != "approve" for item in recommendations_payload["recommendations"])
