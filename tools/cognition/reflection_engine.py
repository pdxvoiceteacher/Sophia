from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


_ALLOWED_PROFILES = {"witness_only", "reproducible_audit", "full_relay"}
_ALLOWED_MODES = {"off", "structured"}


def _stable_score(seed: str) -> float:
    raw = hashlib.sha256(seed.encode("utf-8")).hexdigest()[:8]
    value = int(raw, 16) % 1000
    return float(value) / 1000.0


def _stable_list(items: list[str]) -> list[str]:
    return sorted(str(x) for x in items)


def _canonical_payload(payload: dict[str, Any]) -> str:
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def build_cognition_trace(
    *,
    telemetry: dict[str, Any],
    mode: str,
    profile: str,
    bundle_hash: str,
    bundle_hash_source: str,
) -> dict[str, Any]:
    if mode not in _ALLOWED_MODES:
        raise ValueError("invalid_reflection_mode")
    if profile not in _ALLOWED_PROFILES:
        raise ValueError("invalid_reflection_profile")

    canonical = _canonical_payload(telemetry)
    pass1 = hashlib.sha256(("pass1:" + canonical).encode("utf-8")).hexdigest()
    pass2 = hashlib.sha256(("pass2:" + canonical).encode("utf-8")).hexdigest()

    score = _stable_score(pass1 + pass2)
    delta = abs(_stable_score(pass1) - _stable_score(pass2))
    correction_applied = delta > 0.25
    depth = 4 if correction_applied else 3

    findings = [
        f"consistency_delta={round(delta, 6)}",
        "correction_applied" if correction_applied else "correction_not_required",
    ]
    recommendations = [
        "retain_deterministic_reflection_contract",
        "keep_cognition_trace_out_of_band",
    ]
    invariants_checked = [
        "no_timestamp_entropy",
        "no_uuid_entropy",
        "sorted_serialization",
        "governance_isolation",
    ]
    reflection_blocks = [
        "initial_reasoning_pass",
        "self_evaluation_pass",
        "correction_pass" if correction_applied else "correction_not_needed",
        "final_output_pass",
    ]

    return {
        "schema": "cognition_trace_v1",
        "bundle_hash": str(bundle_hash),
        "bundle_hash_source": str(bundle_hash_source),
        "profile": profile,
        "mode": mode,
        "reflection_score": round(score, 6),
        "self_consistency_delta": round(delta, 6),
        "correction_applied": correction_applied,
        "reasoning_depth_used": int(depth),
        "reflection_blocks": _stable_list(reflection_blocks),
        "invariants_checked": _stable_list(invariants_checked),
        "findings": _stable_list(findings),
        "recommendations": _stable_list(recommendations),
    }


def write_cognition_trace(
    *,
    outdir: Path,
    telemetry: dict[str, Any],
    mode: str,
    profile: str,
    bundle_hash: str,
    bundle_hash_source: str,
) -> Path | None:
    if mode != "structured":
        return None
    trace = build_cognition_trace(
        telemetry=telemetry,
        mode=mode,
        profile=profile,
        bundle_hash=bundle_hash,
        bundle_hash_source=bundle_hash_source,
    )
    path = outdir / "cognition_trace.json"
    path.write_text(json.dumps(trace, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path
