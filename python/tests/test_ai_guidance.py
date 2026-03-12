from __future__ import annotations

import json
from pathlib import Path

import pytest

from sophia.build_ai_guidance import build_ai_guidance


def test_ai_guidance_no_input(tmp_path: Path) -> None:
    g = build_ai_guidance(str(tmp_path), None)
    assert g == {
        "noveltyWeight": 0.0,
        "pluralityWeight": 0.0,
        "humilityWeight": 0.0,
        "requiresHumanReview": False,
    }


def test_ai_guidance_with_docket_and_modifiers(tmp_path: Path) -> None:
    (tmp_path / "bridge").mkdir(parents=True)
    (tmp_path / "bridge" / "cascade_audit.json").write_text(
        json.dumps({"findings": [{"id": "cascade.healthLow", "advisory": "docket"}]}),
        encoding="utf-8",
    )
    (tmp_path / "bridge" / "discovery_corridor_audit.json").write_text(
        json.dumps({"findings": [{"id": "discovery_corridor.lowPotential", "advisory": "watch"}]}),
        encoding="utf-8",
    )
    g = build_ai_guidance(str(tmp_path), None)
    assert g["noveltyWeight"] == pytest.approx(0.4)
    assert g["pluralityWeight"] == pytest.approx(0.2)
    assert g["humilityWeight"] == pytest.approx(0.0)
    assert g["requiresHumanReview"] is True


def test_ai_guidance_writes_output(tmp_path: Path) -> None:
    out = tmp_path / "bridge" / "ai_guidance.json"
    build_ai_guidance(str(tmp_path), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert "noveltyWeight" in payload
