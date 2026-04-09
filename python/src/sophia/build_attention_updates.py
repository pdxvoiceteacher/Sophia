from __future__ import annotations

import argparse
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

from sophia.attention_contract import derive_grounding_inputs, has_minimum_provenance, load_upstream_artifacts

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema" / "bridge" / "attention_updates.schema.json"


GENERIC_ACRONYM_TOKENS = {"tches", "api", "sql", "etl", "json"}


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def _review_priority(*, grounding_active: bool, citation_count: int, has_provenance: bool) -> str:
    if not has_provenance:
        return "docket"
    if grounding_active and citation_count <= 0:
        return "watch"
    return "focus"


def _coherence_targets(coherence_drift_map: dict[str, Any]) -> list[dict[str, Any]]:
    rows = coherence_drift_map.get("nodes")
    if not isinstance(rows, list):
        return []

    targets: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        target_id = row.get("id") or row.get("targetId") or row.get("node_id")
        drift = row.get("driftScore")
        if not isinstance(target_id, str) or not isinstance(drift, (int, float)):
            continue
        if float(drift) >= 0.45:
            targets.append(
                {
                    "target_id": target_id,
                    "priority": "high" if float(drift) >= 0.75 else "medium",
                    "reason": "coherence_drift_guard",
                    "drift_score": round(float(drift), 6),
                }
            )
    return targets


def _is_generic_acronym_clarification(clarification: dict[str, Any]) -> bool:
    reason = str(clarification.get("reason") or clarification.get("kind") or "").lower()
    if "acronym" in reason and "local" not in reason:
        return True
    question = str(clarification.get("question") or "").lower()
    tokens = {tok.strip(" ?!.,") for tok in question.split()}
    return bool(tokens & GENERIC_ACRONYM_TOKENS)


def build_attention_updates(bridge_root: str) -> tuple[dict[str, Any], dict[str, Any]]:
    root = Path(bridge_root)
    bridge_dir = root / "bridge"
    artifacts = load_upstream_artifacts(root)

    grounding_inputs = derive_grounding_inputs(artifacts)
    has_provenance = has_minimum_provenance(grounding_inputs)

    clarification = artifacts.get("clarification_request.json", {})
    drift_map = artifacts.get("coherence_drift_map.json", {})

    targets = _coherence_targets(drift_map)
    if not has_provenance:
        targets = []

    clarification_passthrough: dict[str, Any] | None = None
    if isinstance(clarification, dict) and clarification:
        if grounding_inputs["grounding_active"] and grounding_inputs["citation_count"] > 0 and _is_generic_acronym_clarification(clarification):
            clarification_passthrough = None
        else:
            request_hashes = clarification.get("request_hashes")
            bundle_hashes = clarification.get("bundle_hashes")
            if isinstance(request_hashes, list) and isinstance(bundle_hashes, list):
                clarification_passthrough = {
                    "reason": clarification.get("reason"),
                    "request_hashes": request_hashes,
                    "bundle_hashes": bundle_hashes,
                }

    payload: dict[str, Any] = {
        "schema": "attention_updates_v2",
        "created_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "raw_request_sha256": grounding_inputs["raw_request_sha256"],
        "nav01_question_sha256": grounding_inputs["nav01_question_sha256"],
        "normalized_sha256s": grounding_inputs["normalized_sha256s"],
        "grounding_active": grounding_inputs["grounding_active"],
        "citation_count": grounding_inputs["citation_count"],
        "executive_attention_targets": targets,
        "review_priority": _review_priority(
            grounding_active=grounding_inputs["grounding_active"],
            citation_count=grounding_inputs["citation_count"],
            has_provenance=has_provenance,
        ),
        "semanticMode": "non-executive",
        "upstream_consumed": sorted(artifacts.keys()),
    }
    if clarification_passthrough is not None:
        payload["clarification_request"] = clarification_passthrough

    summary = {
        "schema": "attention_update_summary_v2",
        "created_at": payload["created_at"],
        "raw_request_sha256": payload["raw_request_sha256"],
        "nav01_question_sha256": payload["nav01_question_sha256"],
        "review_priority": payload["review_priority"],
        "executive_target_count": len(payload["executive_attention_targets"]),
        "grounding_active": payload["grounding_active"],
        "citation_count": payload["citation_count"],
    }

    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(payload)

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
