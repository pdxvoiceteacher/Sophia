from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any


def _stable_task_rows(trace: dict[str, Any], recall: dict[str, Any], graph: dict[str, Any]) -> list[tuple[str, int]]:
    base = [
        ("retain_out_of_band_cognition_isolation", 0),
        ("verify_recall_references_exist_in_graph", 1),
        ("maintain_deterministic_serialization_contract", 2),
    ]
    occurrences = int(recall.get("bundle_hash_occurrences") or 0)
    if occurrences == 0:
        base.append(("record_empty_recall_without_governance_effect", 3))
    if occurrences > 1:
        base.append(("review_multi_recall_bundle_links", 3))

    edge_count = len(graph.get("edges") if isinstance(graph.get("edges"), list) else [])
    if edge_count > 0:
        base.append(("confirm_recalled_edges_are_stable_sorted", 4))

    # deterministic ordering and dedupe
    seen = set()
    out: list[tuple[str, int]] = []
    for name, prio in sorted(base, key=lambda x: (int(x[1]), str(x[0]))):
        if name in seen:
            continue
        seen.add(name)
        out.append((name, int(prio)))
    return out


def build_task_plan(
    *,
    trace: dict[str, Any],
    recall: dict[str, Any],
    graph: dict[str, Any],
    bundle_hash: str,
    bundle_hash_source: str,
    profile: str,
    mode: str,
) -> dict[str, Any]:
    rows = _stable_task_rows(trace, recall, graph)
    tasks = [
        {
            "task_id": f"task_{i:03d}",
            "task": name,
            "priority": int(priority),
        }
        for i, (name, priority) in enumerate(rows, start=1)
    ]
    return {
        "schema": "cognition_task_plan_v1",
        "bundle_hash": str(bundle_hash),
        "bundle_hash_source": str(bundle_hash_source),
        "profile": str(profile),
        "mode": str(mode),
        "inputs": {
            "trace_schema": str(trace.get("schema") or ""),
            "recall_schema": str(recall.get("schema") or ""),
            "graph_schema": str(graph.get("schema") or ""),
            "trace_node_id": str(recall.get("trace_node_id") or ""),
            "bundle_hash_occurrences": int(recall.get("bundle_hash_occurrences") or 0),
        },
        "tasks": tasks,
    }


def write_task_plan(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    fd, tmp_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(text)
        os.replace(tmp_name, path)
    finally:
        try:
            if os.path.exists(tmp_name):
                os.unlink(tmp_name)
        except Exception:
            pass
