#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List

from jsonschema import Draft202012Validator


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def load_jsonl(path: Path) -> List[dict]:
    out: List[dict] = []
    if not path.exists():
        return out
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            out.append(json.loads(line))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True, help="Run directory containing telemetry.json")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--out", default="", help="Output path (default: <run-dir>/epistemic_graph.json)")
    ap.add_argument("--schema", default="schema/epistemic_graph.schema.json")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    run_dir = Path(args.run_dir).resolve()
    tele_path = run_dir / "telemetry.json"
    if not tele_path.exists():
        raise SystemExit(f"[build_epistemic_graph] FAIL missing telemetry.json at {tele_path}")

    tele = load_json(tele_path)
    run_id = tele.get("run_id", run_dir.name)

    nodes: List[Dict[str, Any]] = []
    edges: List[Dict[str, Any]] = []

    def add_node(node_id: str, kind: str, data: dict | None = None) -> None:
        nodes.append({"id": node_id, "kind": kind, "data": data})

    def add_edge(src: str, dst: str, kind: str, data: dict | None = None) -> None:
        edges.append({"src": src, "dst": dst, "kind": kind, "data": data})

    run_node = f"run:{run_id}"
    add_node(run_node, "run", {"path": str(run_dir).replace("\\", "/")})

    # Artifacts
    artifacts = tele.get("artifacts") or []
    for a in artifacts:
        p = str(a.get("path", "")).replace("\\", "/")
        aid = f"artifact:{p}"
        add_node(aid, "artifact", {"path": p, "sha256": a.get("sha256")})
        add_edge(run_node, aid, "produced")

    # Claims
    claims = tele.get("claims") or []
    for c in claims:
        cid = str(c.get("id"))
        cnode = f"claim:{cid}"
        add_node(cnode, "claim", c)
        add_edge(cnode, run_node, "asserted_in")
        for evp in c.get("evidence", []) or []:
            evp = str(evp).replace("\\", "/")
            add_edge(cnode, f"artifact:{evp}", "evidenced_by")
        for evp in c.get("counterevidence", []) or []:
            evp = str(evp).replace("\\", "/")
            add_edge(cnode, f"artifact:{evp}", "evidenced_by", {"polarity": "counter"})

    # TEL events
    tel_events = load_jsonl(run_dir / "tel_events.jsonl")
    for i, ev in enumerate(tel_events):
        nid = f"event:tel:{i}"
        add_node(nid, "tel_event", ev)
        add_edge(run_node, nid, "emitted")

    # UCC events
    ucc_events = load_jsonl(run_dir / "ucc_tel_events.jsonl")
    for i, ev in enumerate(ucc_events):
        nid = f"event:ucc:{i}"
        add_node(nid, "ucc_event", ev)
        add_edge(run_node, nid, "emitted")

    # Deterministic ordering
    nodes_sorted = sorted(nodes, key=lambda x: (x["kind"], x["id"]))
    edges_sorted = sorted(edges, key=lambda x: (x["kind"], x["src"], x["dst"]))

    graph = {
        "schema": "epistemic_graph_v1",
        "run_id": run_id,
        "nodes": nodes_sorted,
        "edges": edges_sorted,
    }

    out_path = Path(args.out) if args.out else (run_dir / "epistemic_graph.json")
    out_path.write_text(json.dumps(graph, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")

    # Validate
    schema = load_json(repo / args.schema)
    Draft202012Validator(schema).validate(graph)

    print(f"[build_epistemic_graph] OK wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
