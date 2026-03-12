from __future__ import annotations

import json
from pathlib import Path

from sophia.build_ai_guidance import build_ai_guidance


def test_guidance_weights(tmp_path: Path) -> None:
    cascade = {
        "findings": [
            {
                "id": "cascade.healthLow",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": "",
                "data": {},
            }
        ]
    }
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "cascade_audit.json").write_text(json.dumps(cascade), encoding="utf-8")
    guidance = build_ai_guidance(str(tmp_path))
    assert 0 < guidance["pluralityWeight"] <= 1
    assert guidance["requiresHumanReview"] is False


def test_guidance_docket(tmp_path: Path) -> None:
    lowp = {
        "findings": [
            {
                "id": "discovery_corridor.lowPotential",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": "",
                "data": {},
            }
        ]
    }
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "discovery_corridor_audit.json").write_text(json.dumps(lowp), encoding="utf-8")
    guidance = build_ai_guidance(str(tmp_path))
    assert guidance["requiresHumanReview"] is True
