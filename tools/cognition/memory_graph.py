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


def update_memory_graph(graph: dict[str, Any], cognition_trace: dict[str, Any]) -> dict[str, Any]:
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
    return _norm_graph(g)


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
