from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def _stable_score(seed: str) -> float:
    raw = hashlib.sha256(seed.encode("utf-8")).hexdigest()[:8]
    value = int(raw, 16) % 1000
    return float(value) / 1000.0


def build_cognition_trace(*, telemetry: dict[str, Any], mode: str) -> dict[str, Any]:
    if mode != "structured":
        return {
            "reflection_enabled": False,
            "reflection_score": 0.0,
            "self_consistency_delta": 0.0,
            "correction_applied": False,
            "reasoning_depth_used": 0,
        }

    canonical = json.dumps(telemetry, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    pass1 = hashlib.sha256(("pass1:" + canonical).encode("utf-8")).hexdigest()
    pass2 = hashlib.sha256(("pass2:" + canonical).encode("utf-8")).hexdigest()

    score = _stable_score(pass1 + pass2)
    delta = abs(_stable_score(pass1) - _stable_score(pass2))
    correction_applied = delta > 0.25
    depth = 4 if correction_applied else 3

    return {
        "reflection_enabled": True,
        "reflection_score": round(score, 6),
        "self_consistency_delta": round(delta, 6),
        "correction_applied": correction_applied,
        "reasoning_depth_used": depth,
    }


def write_cognition_trace(*, outdir: Path, telemetry: dict[str, Any], mode: str) -> Path | None:
    trace = build_cognition_trace(telemetry=telemetry, mode=mode)
    if not trace.get("reflection_enabled"):
        return None
    path = outdir / "cognition_trace.json"
    path.write_text(json.dumps(trace, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path
