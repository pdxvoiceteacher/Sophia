from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_resilience_state

REPO = Path(__file__).resolve().parents[1]


def test_resilience_outputs_validate_and_are_sorted() -> None:
    rc = audit_resilience_state.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "resilience_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "succession_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "resilience_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "succession_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row.get("resilienceId", row.get("reviewerId", "")) for row in audit_payload["records"]]
    assert ids == sorted(ids)

    first = recommendations_payload["recommendations"][0]
    assert first["resilienceStatus"] in {"stable", "thinning", "fragile", "capture-risk", "degraded"}
    assert first["auditStatus"] in {
        "continue",
        "queue-continuity-review",
        "increase-watch",
        "freeze-governance-expansion",
        "degraded-mode",
        "require-human-emergency-review",
    }
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_resilience_caution_is_lawful_non_automatic() -> None:
    audit_payload = json.loads((REPO / "bridge" / "resilience_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "succession_recommendations.json").read_text(encoding="utf-8"))

    caution1 = audit_payload.get("caution", "").lower()
    caution2 = recommendations_payload.get("caution", "").lower()

    assert "lawful resilience" in caution1
    assert "no automatic authority transfer" in caution1
    assert "not sovereignty" in caution2
    assert "human/community reviewed" in caution2
