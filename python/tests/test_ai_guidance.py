from __future__ import annotations

import json
from pathlib import Path

from sophia.build_ai_guidance import build_ai_guidance


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def _seed_attention_inputs(root: Path) -> None:
    bridge = root / "bridge"
    _write(
        bridge / "triadic_run_manifest.json",
        {
            "raw_request_sha256": "raw-hash",
            "nav01_question_sha256": "nav-hash",
            "normalized_sha256s": ["norm-hash"],
        },
    )
    _write(bridge / "coherence_drift_map.json", {"nodes": []})
    _write(bridge / "grounding_policy.json", {"grounding_active": True})
    _write(bridge / "source_evidence_packet.json", {"citations": [{"id": "c1"}]})


def test_build_ai_guidance(tmp_path: Path) -> None:
    _seed_attention_inputs(tmp_path)
    cascade_audit = {"findings": [{"id": "cascade.healthLow", "advisory": "watch"}]}
    corr_audit = {"findings": [{"id": "discovery_corridor.lowPotential", "advisory": "watch"}]}
    _write(tmp_path / "cascade_audit.json", cascade_audit)
    _write(tmp_path / "discovery_corridor_audit.json", corr_audit)

    guidance = build_ai_guidance(str(tmp_path))
    assert 0 < guidance["noveltyWeight"] <= 1
    assert 0 < guidance["pluralityWeight"] <= 1
    assert guidance["requiresHumanReview"] is False


def test_build_ai_guidance_docket_sets_review(tmp_path: Path) -> None:
    _seed_attention_inputs(tmp_path)
    _write(tmp_path / "cascade_audit.json", {"findings": [{"id": "capture.riskHigh", "advisory": "watch"}]})
    _write(tmp_path / "discovery_corridor_audit.json", {"findings": [{"id": "discovery_corridor.lowPotential", "advisory": "docket"}]})

    guidance = build_ai_guidance(str(tmp_path))
    assert guidance["humilityWeight"] > 0
    assert guidance["requiresHumanReview"] is True
