from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_scenario_state

REPO = Path(__file__).resolve().parents[1]


def test_scenario_outputs_validate_and_are_sorted() -> None:
    rc = audit_scenario_state.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "scenario_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "scenario_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "scenario_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads((REPO / "schema" / "scenario_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row["scenarioId"] for row in audit_payload["records"]]
    assert ids == sorted(ids)

    first = recommendations_payload["recommendations"][0]
    assert first["scenarioStatus"] in {"stable", "strained", "degraded", "capture-risk", "freeze-recommended"}
    assert first["preparednessRecommendation"] in {
        "continue",
        "harden-watch",
        "rehearse-recovery",
        "freeze-pathway",
        "prioritize-redundancy",
        "require-broader-human-review",
    }
    assert first["targetPublisherAction"] in {"docket", "watch", "suppress"}


def test_scenario_caution_is_hypothetical_non_executing() -> None:
    audit_payload = json.loads((REPO / "bridge" / "scenario_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "scenario_recommendations.json").read_text(encoding="utf-8"))

    c1 = audit_payload.get("caution", "").lower()
    c2 = recommendations_payload.get("caution", "").lower()

    assert "hypothetical preparedness" in c1
    assert "do not authorize live emergency power" in c1
    assert "non-executing" in c2
    assert "no automatic emergency activation" in c2
