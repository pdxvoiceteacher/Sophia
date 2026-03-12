from __future__ import annotations

from sophia.build_ai_guidance import build_ai_guidance


def test_guidance_weights() -> None:
    cascade = {"findings": [{"id": "cascade.healthLow", "advisory": "watch"}]}
    corridor = {"findings": [{"id": "discovery_corridor.lowPotential", "advisory": "docket"}]}
    guidance = build_ai_guidance(cascade, corridor)
    assert guidance["noveltyWeight"] > 0
    assert guidance["requiresHumanReview"] is True


def test_guidance_capture_modifier() -> None:
    cascade = {"findings": [{"id": "capture.riskHigh", "advisory": "watch"}]}
    corridor = {"findings": []}
    guidance = build_ai_guidance(cascade, corridor)
    assert guidance["pluralityWeight"] > 0
