from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_deliberation_quorum

REPO = Path(__file__).resolve().parents[1]


def test_deliberation_quorum_outputs_validate_and_are_sorted() -> None:
    rc = audit_deliberation_quorum.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "quorum_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "amendment_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "quorum_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "amendment_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row.get("deliberationId", row.get("amendmentId", "")) for row in audit_payload["records"]]
    assert ids == sorted(ids)

    first = recommendations_payload["recommendations"][0]
    assert first["quorumStatus"] in {"sufficient", "strained", "stacked-risk", "insufficient", "indeterminate"}
    assert first["amendmentStatus"] in {
        "recommend-deliberation",
        "hold",
        "watch",
        "reject-amendment",
        "require-broader-human-review",
        "emergency-interpretation-only",
    }
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_deliberation_quorum_caution_is_non_automatic() -> None:
    audit_payload = json.loads((REPO / "bridge" / "quorum_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "amendment_recommendations.json").read_text(encoding="utf-8"))

    caution1 = audit_payload.get("caution", "").lower()
    caution2 = recommendations_payload.get("caution", "").lower()

    assert "advisory only" in caution1
    assert "anti-capture" in caution1
    assert "no constitutional revision is automatic" in caution2
    assert "not equivalent to amendment" in caution2
