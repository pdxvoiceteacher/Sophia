from __future__ import annotations

import json
from pathlib import Path

from sophia.build_attention_updates import build_attention_updates


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_attention_updates_uses_grounding_provenance_and_citations(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"

    _write(
        bridge / "triadic_run_manifest.json",
        {
            "raw_request_sha256": "raw-1",
            "nav01_question_sha256": "nav-1",
            "normalized_sha256s": ["AA", "bb", "aa"],
        },
    )
    _write(bridge / "grounding_policy.json", {"grounding_active": True})
    _write(bridge / "source_evidence_packet.json", {"citations": [{"id": "c1"}, {"id": "c2"}]})
    _write(bridge / "context_assessment.json", {"ingress_hardening_needed": False, "clarification_state": "ambiguous"})
    _write(
        bridge / "clarification_request.json",
        {
            "state": "generic_ambiguity",
            "reason": "acronym_ambiguity",
        },
    )

    payload, summary = build_attention_updates(str(tmp_path))

    assert payload["grounding_active"] is True
    assert payload["grounding_count"] == 2
    assert payload["normalized_sha256s"] == ["aa", "bb"]
    assert payload["citation_count"] == 2
    assert payload["citation_ready"] is True
    assert payload["clarification_state"] == "source_resolved"
    assert payload["ingress_hardening_needed"] is False
    assert payload["review_priority"] == "normal"

    assert summary["clarification_state"] == "source_resolved"
    assert summary["citation_ready"] is True

    out_payload = json.loads((bridge / "attention_updates.json").read_text(encoding="utf-8"))
    out_summary = json.loads((bridge / "attention_update_summary.json").read_text(encoding="utf-8"))
    assert out_payload == payload
    assert out_summary == summary
