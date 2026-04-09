from __future__ import annotations

import json
from pathlib import Path

from sophia.build_attention_updates import build_attention_updates


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_grounded_run_avoids_generic_acronym_reclarification(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(
        bridge / "triadic_run_manifest.json",
        {
            "raw_request_sha256": "raw-hash",
            "nav01_question_sha256": "nav-hash",
            "normalized_sha256s": ["norm-hash"],
        },
    )
    _write(bridge / "grounding_policy.json", {"grounding_active": True})
    _write(bridge / "source_evidence_packet.json", {"citations": [{"id": "c1"}]})
    _write(bridge / "coherence_drift_map.json", {"nodes": []})
    _write(
        bridge / "clarification_request.json",
        {
            "reason": "acronym_ambiguity",
            "question": "What does TCHES mean?",
            "request_hashes": ["rq-1"],
            "bundle_hashes": ["bundle-1"],
        },
    )

    payload, _ = build_attention_updates(str(tmp_path))

    assert "clarification_request" not in payload


def test_local_definition_clarification_passthrough_preserves_hashes(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(
        bridge / "triadic_run_manifest.json",
        {
            "raw_request_sha256": "raw-hash",
            "nav01_question_sha256": "nav-hash",
            "normalized_sha256s": ["norm-hash"],
        },
    )
    _write(bridge / "grounding_policy.json", {"grounding_active": True})
    _write(bridge / "source_evidence_packet.json", {"citations": []})
    _write(bridge / "coherence_drift_map.json", {"nodes": []})
    _write(
        bridge / "clarification_request.json",
        {
            "reason": "local_definition_unresolved",
            "request_hashes": ["rq-1", "rq-2"],
            "bundle_hashes": ["bundle-1"],
        },
    )

    payload, _ = build_attention_updates(str(tmp_path))

    assert payload["review_priority"] == "watch"
    assert payload["clarification_request"]["request_hashes"] == ["rq-1", "rq-2"]
    assert payload["clarification_request"]["bundle_hashes"] == ["bundle-1"]
