from __future__ import annotations

import json
from pathlib import Path

from sophia.build_attention_updates import build_attention_updates


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_build_attention_updates_emits_contract_and_summary(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"

    _write(
        bridge / "triadic_run_manifest.json",
        {
            "raw_request_sha256": "raw-hash-1",
            "nav01_question_sha256": "nav-hash-1",
            "normalized_sha256s": ["norm-1", "norm-2"],
        },
    )
    _write(bridge / "grounding_policy.json", {"grounding_active": True})
    _write(bridge / "source_evidence_packet.json", {"citations": [{"id": "c1"}, {"id": "c2"}]})
    _write(
        bridge / "coherence_drift_map.json",
        {"nodes": [{"id": "TCHES", "driftScore": 0.2}, {"id": "route-x", "driftScore": 0.8}]},
    )

    payload, summary = build_attention_updates(str(tmp_path))

    assert payload["raw_request_sha256"] == "raw-hash-1"
    assert payload["nav01_question_sha256"] == "nav-hash-1"
    assert payload["normalized_sha256s"] == ["norm-1", "norm-2"]
    assert payload["grounding_active"] is True
    assert payload["citation_count"] == 2
    assert payload["semanticMode"] == "non-executive"
    assert payload["review_priority"] == "focus"
    assert len(payload["executive_attention_targets"]) == 1

    out_payload = json.loads((bridge / "attention_updates.json").read_text(encoding="utf-8"))
    out_summary = json.loads((bridge / "attention_update_summary.json").read_text(encoding="utf-8"))
    assert out_payload == payload
    assert out_summary == summary


def test_missing_provenance_forces_docket_and_no_targets(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"

    _write(bridge / "grounding_policy.json", {"grounding_active": True})
    _write(bridge / "source_evidence_packet.json", {"citations": [{"id": "c1"}]})
    _write(bridge / "coherence_drift_map.json", {"nodes": [{"id": "x", "driftScore": 0.9}]})

    payload, _ = build_attention_updates(str(tmp_path))

    assert payload["review_priority"] == "docket"
    assert payload["executive_attention_targets"] == []
