from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_reviewer_behavior

REPO = Path(__file__).resolve().parents[1]


def test_reviewer_behavior_outputs_validate_and_are_sorted() -> None:
    rc = audit_reviewer_behavior.main()
    assert rc == 0

    payload = json.loads((REPO / "bridge" / "reviewer_behavior_audit.json").read_text(encoding="utf-8"))
    schema = json.loads((REPO / "schema" / "reviewer_behavior_audit_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(schema).validate(payload)

    reviewer_ids = [row["reviewerId"] for row in payload["reviewers"]]
    assert reviewer_ids == sorted(reviewer_ids)
    assert payload["reviewers"][0]["continuedEligibilityStatus"] in {"continue", "watch", "re-review", "suspend-pending-review"}


def test_reviewer_behavior_is_reversible_and_auditable() -> None:
    payload = json.loads((REPO / "bridge" / "reviewer_behavior_audit.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "advisory" in caution
    assert "reversible" in caution
