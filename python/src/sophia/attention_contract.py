from __future__ import annotations

import json
from pathlib import Path
from typing import Any

REQUIRED_UPSTREAM_FILES = (
    "triadic_run_manifest.json",
    "coherence_drift_map.json",
    "grounding_policy.json",
    "source_evidence_packet.json",
    "clarification_request.json",
)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _as_list_of_str(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    out: list[str] = []
    for item in value:
        if isinstance(item, str) and item:
            out.append(item)
    return out


def _as_bool(value: Any, *, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    return default


def _as_float(value: Any, *, default: float = 0.0) -> float:
    if isinstance(value, (int, float)):
        return float(value)
    return default


def _extract_hashes(manifest: dict[str, Any]) -> tuple[str | None, str | None, list[str]]:
    raw_request_sha256 = manifest.get("raw_request_sha256")
    nav01_question_sha256 = manifest.get("nav01_question_sha256")
    normalized_sha256s = manifest.get("normalized_sha256s")

    if not isinstance(raw_request_sha256, str):
        raw_request_sha256 = None
    if not isinstance(nav01_question_sha256, str):
        nav01_question_sha256 = None

    if not isinstance(normalized_sha256s, list):
        request = manifest.get("request")
        if isinstance(request, dict):
            normalized_sha256s = request.get("normalized_sha256s")

    return raw_request_sha256, nav01_question_sha256, _as_list_of_str(normalized_sha256s)


def load_upstream_artifacts(bridge_root: Path) -> dict[str, dict[str, Any]]:
    bridge_dir = bridge_root / "bridge"
    artifacts: dict[str, dict[str, Any]] = {}
    for filename in REQUIRED_UPSTREAM_FILES:
        path = bridge_dir / filename
        if path.exists():
            artifacts[filename] = _load_json(path)
    return artifacts


def derive_grounding_inputs(artifacts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    manifest = artifacts.get("triadic_run_manifest.json", {})
    grounding_policy = artifacts.get("grounding_policy.json", {})
    evidence_packet = artifacts.get("source_evidence_packet.json", {})

    raw_request_sha256, nav01_question_sha256, normalized_sha256s = _extract_hashes(manifest)

    grounding_active = _as_bool(grounding_policy.get("grounding_active"), default=False)
    citations = evidence_packet.get("citations")
    citation_count = len(citations) if isinstance(citations, list) else int(_as_float(evidence_packet.get("citation_count"), default=0.0))

    return {
        "raw_request_sha256": raw_request_sha256,
        "nav01_question_sha256": nav01_question_sha256,
        "normalized_sha256s": normalized_sha256s,
        "grounding_active": grounding_active,
        "citation_count": max(0, citation_count),
    }


def has_minimum_provenance(payload: dict[str, Any]) -> bool:
    if not isinstance(payload.get("raw_request_sha256"), str):
        return False
    if not isinstance(payload.get("nav01_question_sha256"), str):
        return False
    normalized = payload.get("normalized_sha256s")
    return isinstance(normalized, list) and len(normalized) > 0
