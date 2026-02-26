from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from tools.cognition.memory_graph import load_memory_graph


_EMPTY_RECALL = {
    "schema": "cognition_memory_recall_v1",
    "bundle_hash": "",
    "trace_node_id": "",
    "matched_bundle_node_id": "",
    "bundle_hash_occurrences": 0,
    "recalled_node_ids": [],
    "recalled_edge_ids": [],
    "invariants_checked": [
        "governance_isolation",
        "no_runtime_entropy",
        "sorted_serialization",
    ],
}


def _stable_list(values: list[str]) -> list[str]:
    return sorted(str(v) for v in values)


def build_memory_recall(graph: dict[str, Any], bundle_hash: str) -> dict[str, Any]:
    bundle_hash_s = str(bundle_hash)
    idx = [
        i
        for i in (graph.get("bundle_hash_index") if isinstance(graph.get("bundle_hash_index"), list) else [])
        if isinstance(i, dict) and str(i.get("bundle_hash", "")) == bundle_hash_s
    ]
    trace_node_ids = _stable_list([str(i.get("node_id", "")) for i in idx if str(i.get("node_id", ""))])

    bundle_node_id = ""
    nodes = graph.get("nodes") if isinstance(graph.get("nodes"), list) else []
    for node in sorted((n for n in nodes if isinstance(n, dict)), key=lambda n: str(n.get("node_id", ""))):
        node_id = str(node.get("node_id", ""))
        if node_id.startswith("bundle_") and str(node.get("label", "")) == bundle_hash_s:
            bundle_node_id = node_id
            break

    edges = graph.get("edges") if isinstance(graph.get("edges"), list) else []
    recalled_edge_ids = []
    for edge in sorted((e for e in edges if isinstance(e, dict)), key=lambda e: str(e.get("edge_id", ""))):
        source = str(edge.get("source", ""))
        target = str(edge.get("target", ""))
        if source == bundle_node_id and target in trace_node_ids:
            edge_id = str(edge.get("edge_id", ""))
            if edge_id:
                recalled_edge_ids.append(edge_id)

    recall = dict(_EMPTY_RECALL)
    recall["bundle_hash"] = bundle_hash_s
    recall["trace_node_id"] = trace_node_ids[0] if trace_node_ids else ""
    recall["matched_bundle_node_id"] = bundle_node_id
    recall["bundle_hash_occurrences"] = len(trace_node_ids)
    recall["recalled_node_ids"] = trace_node_ids
    recall["recalled_edge_ids"] = _stable_list(recalled_edge_ids)
    recall["invariants_checked"] = _stable_list(list(_EMPTY_RECALL["invariants_checked"]))
    return recall


def write_memory_recall(*, graph_path: Path, recall_path: Path, bundle_hash: str) -> Path:
    graph = load_memory_graph(graph_path)
    recall = build_memory_recall(graph, bundle_hash)
    recall_path.parent.mkdir(parents=True, exist_ok=True)
    recall_path.write_text(json.dumps(recall, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return recall_path
