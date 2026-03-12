from __future__ import annotations

import json
from pathlib import Path

from sophia.build_ai_guidance import GUIDANCE_TEMPLATE, build_ai_guidance


def test_ai_guidance_no_input(tmp_path: Path) -> None:
    g = build_ai_guidance(str(tmp_path), None)
    assert g == GUIDANCE_TEMPLATE


def test_ai_guidance_with_docket(tmp_path: Path) -> None:
    doc_audit = {"findings": [{"id": "cascade.healthLow", "advisory": "docket"}]}
    (tmp_path / "bridge").mkdir(parents=True)
    (tmp_path / "bridge" / "cascade_audit.json").write_text(json.dumps(doc_audit), encoding="utf-8")
    g2 = build_ai_guidance(str(tmp_path), None)
    assert g2["pluralityWeight"] == 1.0
    assert g2["requiresHumanReview"]


def test_ai_guidance_writes_output(tmp_path: Path) -> None:
    out = tmp_path / "bridge" / "ai_guidance.json"
    build_ai_guidance(str(tmp_path), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert "noveltyWeight" in payload
