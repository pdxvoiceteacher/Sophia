from __future__ import annotations

import argparse
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_bridge_dir(root: Path) -> Path:
    return root if root.name == "bridge" else root / "bridge"


def _as_bool(value: Any, *, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    return default


def _as_int(value: Any, *, default: int = 0) -> int:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    return default


def _normalized_hashes(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    out: list[str] = []
    seen: set[str] = set()
    for item in value:
        if not isinstance(item, str):
            continue
        norm = item.strip().lower()
        if not norm or norm in seen:
            continue
        seen.add(norm)
        out.append(norm)
    return out


def _citation_count(source_evidence_packet: dict[str, Any]) -> int:
    citations = source_evidence_packet.get("citations")
    if isinstance(citations, list):
        return len(citations)
    return max(0, _as_int(source_evidence_packet.get("citation_count"), default=0))


def _clarification_state(
    clarification_request: dict[str, Any],
    context_assessment: dict[str, Any],
    *,
    grounding_active: bool,
    citation_count: int,
) -> str:
    if grounding_active and citation_count > 0:
        # Grounded, citation-bearing runs are source-resolved; do not reintroduce generic ambiguity.
        return "source_resolved"

    candidate = clarification_request.get("clarification_state") or clarification_request.get("state")
    if not isinstance(candidate, str) or not candidate.strip():
        candidate = context_assessment.get("clarification_state") or context_assessment.get("state")
    if isinstance(candidate, str) and candidate.strip():
        return candidate.strip()
    return "needs_clarification"


def build_attention_updates(bridge_root: str) -> tuple[dict[str, Any], dict[str, Any]]:
    root = Path(bridge_root)
    bridge_dir = _resolve_bridge_dir(root)

    manifest = _read_json(bridge_dir / "triadic_run_manifest.json")
    grounding_policy = _read_json(bridge_dir / "grounding_policy.json")
    source_evidence_packet = _read_json(bridge_dir / "source_evidence_packet.json")
    context_assessment = _read_json(bridge_dir / "context_assessment.json")
    clarification_request = _read_json(bridge_dir / "clarification_request.json")

    raw_request_sha256 = manifest.get("raw_request_sha256") if isinstance(manifest.get("raw_request_sha256"), str) else None
    nav01_question_sha256 = manifest.get("nav01_question_sha256") if isinstance(manifest.get("nav01_question_sha256"), str) else None
    normalized_sha256s = _normalized_hashes(manifest.get("normalized_sha256s"))

    grounding_active = _as_bool(grounding_policy.get("grounding_active"), default=False)
    grounding_count = len(normalized_sha256s) if grounding_active else 0
    citation_count = _citation_count(source_evidence_packet)
    citation_ready = grounding_active and citation_count > 0
    clarification_state = _clarification_state(
        clarification_request,
        context_assessment,
        grounding_active=grounding_active,
        citation_count=citation_count,
    )
    ingress_hardening_needed = _as_bool(
        context_assessment.get("ingress_hardening_needed"),
        default=not citation_ready,
    )

    payload: dict[str, Any] = {
        "schema": "attention_updates_v2",
        "created_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "raw_request_sha256": raw_request_sha256,
        "nav01_question_sha256": nav01_question_sha256,
        "grounding_active": grounding_active,
        "grounding_count": grounding_count,
        "normalized_sha256s": normalized_sha256s,
        "citation_count": citation_count,
        "citation_ready": citation_ready,
        "clarification_state": clarification_state,
        "ingress_hardening_needed": ingress_hardening_needed,
        "review_priority": "normal",
        "semanticMode": "non-executive",
    }

    summary = {
        "schema": "attention_update_summary_v2",
        "created_at": payload["created_at"],
        "nav01_question_sha256": nav01_question_sha256,
        "grounding_active": grounding_active,
        "grounding_count": grounding_count,
        "citation_count": citation_count,
        "citation_ready": citation_ready,
        "clarification_state": clarification_state,
        "ingress_hardening_needed": ingress_hardening_needed,
        "review_priority": "normal",
    }

    _write_json(bridge_dir / "attention_updates.json", payload)
    _write_json(bridge_dir / "attention_update_summary.json", summary)

    return payload, summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    args = parser.parse_args(argv)
    build_attention_updates(args.bridge_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
