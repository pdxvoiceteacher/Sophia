from __future__ import annotations

from sophia.build_ai_guidance import build_ai_guidance

from sophia.build_ai_guidance import build_ai_guidance


def test_build_ai_guidance(tmp_path: Path) -> None:
    cascade_audit = {"findings": [{"id": "cascade.healthLow", "advisory": "watch"}]}
    corr_audit = {"findings": [{"id": "discovery_corridor.lowPotential", "advisory": "watch"}]}
    (tmp_path / "cascade_audit.json").write_text(json.dumps(cascade_audit), encoding="utf-8")
    (tmp_path / "discovery_corridor_audit.json").write_text(json.dumps(corr_audit), encoding="utf-8")
    guidance = build_ai_guidance(str(tmp_path))
    assert 0 < guidance["noveltyWeight"] <= 1
    assert 0 < guidance["pluralityWeight"] <= 1
    assert guidance["requiresHumanReview"] is False


def test_build_ai_guidance_docket_sets_review(tmp_path: Path) -> None:
    cascade_audit = {"findings": [{"id": "capture.riskHigh", "advisory": "watch"}]}
    corr_audit = {"findings": [{"id": "discovery_corridor.lowPotential", "advisory": "docket"}]}
    (tmp_path / "cascade_audit.json").write_text(json.dumps(cascade_audit), encoding="utf-8")
    (tmp_path / "discovery_corridor_audit.json").write_text(json.dumps(corr_audit), encoding="utf-8")
    guidance = build_ai_guidance(str(tmp_path))
    assert guidance["humilityWeight"] > 0
    assert guidance["requiresHumanReview"] is True
