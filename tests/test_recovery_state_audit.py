from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_recovery_state

REPO = Path(__file__).resolve().parents[1]


def test_recovery_outputs_validate_and_are_sorted() -> None:
    rc = audit_recovery_state.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "recovery_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "recovery_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "recovery_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "recovery_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row.get("preservationId", row.get("recoveryId", "")) for row in audit_payload["records"]]
    assert ids == sorted(ids)

    first = recommendations_payload["recommendations"][0]
    assert first["recoveryStatus"] in {"maintain", "escrow-review", "watch", "hold", "reject", "require-human-emergency-review"}
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_recovery_caution_is_bounded_anti_tamper() -> None:
    audit_payload = json.loads((REPO / "bridge" / "recovery_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "recovery_recommendations.json").read_text(encoding="utf-8"))

    c1 = audit_payload.get("caution", "").lower()
    c2 = recommendations_payload.get("caution", "").lower()
    assert "anti-tamper" in c1
    assert "no autonomous replication" in c1
    assert "human/community review" in c2
    assert "no self-executing recovery" in c2
