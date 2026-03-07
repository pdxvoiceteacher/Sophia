from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_attestation_state

REPO = Path(__file__).resolve().parents[1]


def test_attestation_outputs_validate_and_are_sorted() -> None:
    rc = audit_attestation_state.main()
    assert rc == 0

    witness_payload = json.loads((REPO / "bridge" / "witness_audit.json").read_text(encoding="utf-8"))
    attestation_payload = json.loads((REPO / "bridge" / "attestation_recommendations.json").read_text(encoding="utf-8"))

    witness_schema = json.loads((REPO / "schema" / "witness_audit_v1.schema.json").read_text(encoding="utf-8"))
    attestation_schema = json.loads((REPO / "schema" / "attestation_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(witness_schema).validate(witness_payload)
    Draft202012Validator(attestation_schema).validate(attestation_payload)

    ids = [row.get("witnessId", row.get("attestationId", "")) for row in witness_payload["records"]]
    assert ids == sorted(ids)

    first = attestation_payload["recommendations"][0]
    assert first["witnessStatus"] in {"sufficient", "strained", "stacked-risk", "insufficient", "indeterminate"}
    assert first["attestationStatus"] in {
        "docket-for-witness",
        "watch",
        "hold",
        "reject-attestation",
        "require-broader-human-review",
    }
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_attestation_cautions_are_advisory_and_non_sovereign() -> None:
    witness_payload = json.loads((REPO / "bridge" / "witness_audit.json").read_text(encoding="utf-8"))
    attestation_payload = json.loads((REPO / "bridge" / "attestation_recommendations.json").read_text(encoding="utf-8"))

    c1 = witness_payload.get("caution", "").lower()
    c2 = attestation_payload.get("caution", "").lower()

    assert "advisory" in c1
    assert "does not transfer sovereignty" in c1
    assert "no automatic state transition" in c2
