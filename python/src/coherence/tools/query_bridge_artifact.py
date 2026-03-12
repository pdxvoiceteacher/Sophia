from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _entry_collections(doc: dict[str, Any]) -> list[tuple[str, list[dict[str, Any]]]]:
    out: list[tuple[str, list[dict[str, Any]]]] = []
    for key in ("targets", "records", "recommendations", "phases", "trace"):
        rows = doc.get(key)
        if isinstance(rows, list):
            out.append((key, [r for r in rows if isinstance(r, dict)]))
    return out


def _status_value(row: dict[str, Any]) -> str | None:
    for k, v in row.items():
        if k.endswith("Status") and isinstance(v, str):
            return v
    return None


def _row_exec_review(row: dict[str, Any]) -> bool:
    if isinstance(row.get("requiresExecutiveReview"), bool):
        return bool(row["requiresExecutiveReview"])
    if row.get("targetPublisherAction") == "docket":
        return True
    status = (_status_value(row) or "").lower()
    return "executive" in status


def _match(
    row: dict[str, Any],
    *,
    target_id: str | None,
    source_id: str | None,
    phase_id: str | None,
    status: str | None,
    requires_exec_review: bool | None,
) -> bool:
    if target_id and str(row.get("targetId")) != target_id:
        return False
    if source_id and str(row.get("sourceId")) != source_id:
        return False
    if phase_id and str(row.get("phaseId")) != phase_id:
        return False
    if status and (_status_value(row) or "") != status:
        return False
    if requires_exec_review is not None and _row_exec_review(row) != requires_exec_review:
        return False
    return True


def query_doc(
    doc: dict[str, Any],
    *,
    target_id: str | None = None,
    source_id: str | None = None,
    phase_id: str | None = None,
    status: str | None = None,
    requires_exec_review: bool | None = None,
    require_divergent_integrity: bool = False,
    require_trust_presentation_degraded: bool = False,
) -> list[dict[str, Any]]:
    metadata = doc.get("metadata") if isinstance(doc.get("metadata"), dict) else {}
    canonical_integrity = metadata.get("canonicalIntegrity") if isinstance(metadata, dict) else {}
    divergence = isinstance(canonical_integrity, dict) and canonical_integrity.get("status") == "divergent"

    trust_degraded = False
    if isinstance(doc.get("trustPresentationDegraded"), bool):
        trust_degraded = bool(doc.get("trustPresentationDegraded"))
    elif isinstance(metadata, dict) and isinstance(metadata.get("trustPresentationDegraded"), bool):
        trust_degraded = bool(metadata.get("trustPresentationDegraded"))

    if require_divergent_integrity and not divergence:
        return []
    if require_trust_presentation_degraded and not trust_degraded:
        return []

    results: list[dict[str, Any]] = []
    for collection_name, rows in _entry_collections(doc):
        for row in rows:
            if _match(
                row,
                target_id=target_id,
                source_id=source_id,
                phase_id=phase_id,
                status=status,
                requires_exec_review=requires_exec_review,
            ):
                results.append(
                    {
                        "collection": collection_name,
                        "schema": doc.get("schema"),
                        "targetId": row.get("targetId"),
                        "sourceId": row.get("sourceId"),
                        "phaseId": row.get("phaseId"),
                        "status": _status_value(row),
                        "requiresExecutiveReview": _row_exec_review(row),
                        "targetPublisherAction": row.get("targetPublisherAction"),
                        "canonicalIntegrityDivergent": divergence,
                        "trustPresentationDegraded": trust_degraded,
                        "row": row,
                    }
                )
    return results


def _print_compact(rows: list[dict[str, Any]]) -> None:
    for row in rows:
        print(
            " | ".join(
                [
                    f"collection={row.get('collection')}",
                    f"targetId={row.get('targetId')}",
                    f"sourceId={row.get('sourceId')}",
                    f"phaseId={row.get('phaseId')}",
                    f"status={row.get('status')}",
                    f"action={row.get('targetPublisherAction')}",
                    f"execReview={row.get('requiresExecutiveReview')}",
                    f"divergent={row.get('canonicalIntegrityDivergent')}",
                    f"trustDegraded={row.get('trustPresentationDegraded')}",
                ]
            )
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Query a bridge artifact by common lineage/status fields")
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--target-id")
    parser.add_argument("--source-id")
    parser.add_argument("--phase-id")
    parser.add_argument("--status")
    parser.add_argument("--requires-executive-review", choices=["true", "false"])
    parser.add_argument("--canonical-divergent", action="store_true")
    parser.add_argument("--trust-presentation-degraded", action="store_true")
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args(argv)

    doc = _load(args.artifact)
    rows = query_doc(
        doc,
        target_id=args.target_id,
        source_id=args.source_id,
        phase_id=args.phase_id,
        status=args.status,
        requires_exec_review=None if args.requires_executive_review is None else args.requires_executive_review == "true",
        require_divergent_integrity=args.canonical_divergent,
        require_trust_presentation_degraded=args.trust_presentation_degraded,
    )

    if args.compact:
        _print_compact(rows)
    else:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
