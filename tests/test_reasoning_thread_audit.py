from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.sophia import audit_reasoning_threads

REPO = Path(__file__).resolve().parents[1]


def test_reasoning_thread_audit_outputs_validate_and_are_sorted() -> None:
    rc = audit_reasoning_threads.main()
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "reasoning_audit.json").read_text(encoding="utf-8"))
    candidates_payload = json.loads((REPO / "bridge" / "recursive_reasoning_candidates.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "reasoning_audit_v1.schema.json").read_text(encoding="utf-8"))
    candidates_schema = json.loads((REPO / "schema" / "recursive_reasoning_candidates_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(candidates_schema).validate(candidates_payload)

    thread_ids = [item["threadId"] for item in audit_payload["threads"]]
    assert thread_ids == sorted(thread_ids)

    first = audit_payload["threads"][0]
    assert first["auditStatus"] in {"observe", "promote", "defer", "reject", "watch"}
    assert first["targetPublisherAction"] in {"annotate", "surface", "hold", "suppress"}
    assert isinstance(first["cognitiveWatchSignals"], list)
    assert first["explanation"]


def test_recursive_candidates_are_cautious_and_non_anthropomorphic() -> None:
    payload = json.loads((REPO / "bridge" / "recursive_reasoning_candidates.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "not an autonomy" in caution
    assert "agi" in caution
