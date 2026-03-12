from __future__ import annotations

import json
from pathlib import Path

from sophia import build_ai_guidance as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_ai_guidance_builds_and_is_bounded(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(
        bridge / "cascade_audit.json",
        {
            "schema": "cascade_audit_v1",
            "created_at": "2026-03-11T00:00:00Z",
            "caution": "bounded",
            "decision": "warn",
            "findings": [
                {"id": "cascade.healthLow", "severity": "warn", "type": "audit", "advisory": "watch", "message": "x", "data": {}}
            ],
        },
    )

    payload = module.build_ai_guidance(bridge_root=tmp_path)
    assert payload["schema"] == "sophia/ai_guidance_v1"
    assert isinstance(payload["modifiers"], list) and len(payload["modifiers"]) >= 1
    assert "increase_plural_exploration" in payload["modifiers"]


def test_ai_guidance_defaults_when_no_inputs(tmp_path: Path) -> None:
    payload = module.build_ai_guidance(bridge_root=tmp_path / "missing")
    assert payload["modifiers"] == ["increase_epistemic_transparency", "avoid_canon_language"]
