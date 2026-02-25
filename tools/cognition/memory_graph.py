from __future__ import annotations

import hashlib
import os
import tempfile
import json
from pathlib import Path
from typing import Any

_EMPTY = {"schema": "cognition_memory_graph_v1", "nodes": [], "edges": [], "bundle_hash_index": []}


def _norm_graph(graph: dict[str, Any]) -> dict[str, Any]:
    nodes = graph.get("nodes") if isinstance(graph.get("nodes"), list) else []
    edges = graph.get("edges") if isinstance(graph.get("edges"), list) else []
    idx = graph.get("bundle_hash_index") if isinstance(graph.get("bundle_hash_index"), list) else []
    return {
        "schema": "cognition_memory_graph_v1",
        "nodes": sorted([n for n in nodes if isinstance(n, dict)], key=lambda x: str(x.get("node_id", ""))),
        "edges": sorted([e for e in edges if isinstance(e, dict)], key=lambda x: str(x.get("edge_id", ""))),
        "bundle_hash_index": sorted(
            [i for i in idx if isinstance(i, dict)],
            key=lambda x: (str(x.get("bundle_hash", "")), str(x.get("node_id", ""))),
        ),
    }


def load_memory_graph(path: Path) -> dict[str, Any]:
    if not path.exists():
        return dict(_EMPTY)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return dict(_EMPTY)
    if not isinstance(payload, dict) or payload.get("schema") != "cognition_memory_graph_v1":
        return dict(_EMPTY)
    return _norm_graph(payload)


def _trace_node_id(cognition_trace: dict[str, Any]) -> str:
    canonical = json.dumps(cognition_trace, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return "trace_" + hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def _to_positive_cap(value: int | None) -> int:
    if value is None:
        return 0
    try:
        n = int(value)
    except Exception:
        return 0
    return n if n > 0 else 0


def _prune_graph(graph: dict[str, Any], *, max_nodes: int = 0, max_edges: int = 0) -> dict[str, Any]:
    g = _norm_graph(graph)
    node_cap = _to_positive_cap(max_nodes)
    edge_cap = _to_positive_cap(max_edges)

    nodes = {str(n.get("node_id", "")): n for n in g["nodes"] if str(n.get("node_id", ""))}
    edges = [e for e in g["edges"] if str(e.get("edge_id", ""))]

    if node_cap and len(nodes) > node_cap:
        degree: dict[str, int] = {node_id: 0 for node_id in nodes}
        for edge in edges:
            source = str(edge.get("source", ""))
            target = str(edge.get("target", ""))
            if source in degree:
                degree[source] += 1
            if target in degree:
                degree[target] += 1

        prune_count = len(nodes) - node_cap
        prune_ids = {
            node_id
            for node_id, _deg in sorted(((nid, degree.get(nid, 0)) for nid in nodes), key=lambda x: (x[1], x[0]))[:prune_count]
        }
        nodes = {nid: n for nid, n in nodes.items() if nid not in prune_ids}
        edges = [
            e
            for e in edges
            if str(e.get("source", "")) not in prune_ids and str(e.get("target", "")) not in prune_ids
        ]
        g["bundle_hash_index"] = [
            i for i in g["bundle_hash_index"] if str(i.get("node_id", "")) and str(i.get("node_id", "")) in nodes
        ]

    if edge_cap and len(edges) > edge_cap:
        keep_edge_ids = {
            str(e.get("edge_id", ""))
            for e in sorted(edges, key=lambda x: str(x.get("edge_id", "")))[len(edges) - edge_cap :]
            if str(e.get("edge_id", ""))
        }
        edges = [e for e in edges if str(e.get("edge_id", "")) in keep_edge_ids]

    g["nodes"] = list(nodes.values())
    g["edges"] = edges
    return _norm_graph(g)


def update_memory_graph(
    graph: dict[str, Any],
    cognition_trace: dict[str, Any],
    *,
    max_nodes: int = 0,
    max_edges: int = 0,
) -> dict[str, Any]:
    g = _norm_graph(graph)
    bundle_hash = str(cognition_trace.get("bundle_hash") or "")
    trace_node = _trace_node_id(cognition_trace)
    bundle_node = f"bundle_{bundle_hash[:16]}"

    nodes = {str(n.get("node_id")): n for n in g["nodes"]}
    nodes.setdefault(bundle_node, {"node_id": bundle_node, "kind": "bundle", "label": bundle_hash})
    nodes.setdefault(trace_node, {"node_id": trace_node, "kind": "cognition_trace", "label": trace_node})

    edge_id = f"edge_{bundle_node}_{trace_node}_has_reflection"
    edges = {str(e.get("edge_id")): e for e in g["edges"]}
    edges.setdefault(
        edge_id,
        {"edge_id": edge_id, "source": bundle_node, "target": trace_node, "relation": "has_reflection"},
    )

    idx_key = (bundle_hash, trace_node)
    index = {(str(i.get("bundle_hash")), str(i.get("node_id"))) for i in g["bundle_hash_index"]}
    if idx_key not in index:
        g["bundle_hash_index"].append({"bundle_hash": bundle_hash, "node_id": trace_node})

    g["nodes"] = list(nodes.values())
    g["edges"] = list(edges.values())
    return _prune_graph(g, max_nodes=max_nodes, max_edges=max_edges)


def write_memory_graph(path: Path, updated_graph: dict[str, Any]) -> None:
    g = _norm_graph(updated_graph)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(g, indent=2, sort_keys=True) + "\n"
    fd, tmp_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(payload)
        os.replace(tmp_name, path)
    finally:
        try:
            if os.path.exists(tmp_name):
                os.unlink(tmp_name)
        except Exception:
            pass
