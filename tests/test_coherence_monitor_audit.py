from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_coherence_monitor

REPO = Path(__file__).resolve().parents[1]


def test_coherence_monitor_audit_outputs_validate_and_sorted() -> None:
    rc = audit_coherence_monitor.main()
    assert rc == 0

    stability = json.loads((REPO / "bridge" / "stability_audit.json").read_text(encoding="utf-8"))
    escalations = json.loads((REPO / "bridge" / "recursive_watch_escalations.json").read_text(encoding="utf-8"))

    stability_schema = json.loads((REPO / "schema" / "stability_audit_v1.schema.json").read_text(encoding="utf-8"))
    escalations_schema = json.loads((REPO / "schema" / "recursive_watch_escalations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(stability_schema).validate(stability)
    Draft202012Validator(escalations_schema).validate(escalations)

    ids = [x["threadId"] for x in stability["threads"]]
    assert ids == sorted(ids)

    first = stability["threads"][0]
    assert first["stabilityStatus"] in {"stable", "oscillating", "degrading", "emerging"}
    assert first["auditStatus"] in {"observe", "promote", "hold", "escalate-human-review", "suppress"}
    assert first["targetPublisherAction"] in {"annotate", "surface", "watch", "hold"}


def test_escalation_artifact_language_is_cautious() -> None:
    payload = json.loads((REPO / "bridge" / "recursive_watch_escalations.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "not autonomy escalation" in caution
