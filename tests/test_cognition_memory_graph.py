from __future__ import annotations

import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.cognition.memory_graph import load_memory_graph, update_memory_graph, write_memory_graph
from tools.telemetry import run_wrapper


ROOT = Path(__file__).resolve().parents[1]


def _seed_weighted_env(tmp_path: Path, bundle_id: str, peers: int = 2) -> None:
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")
    bundle_hash = hashlib.sha256(bundle_id.encode("utf-8")).hexdigest()
    rows: list[dict[str, str]] = []
    local_priv, local_pub = run_wrapper._deterministic_ed25519_keypair("local-attestation-seed")
    (cfg / "local_attestation_key.json").write_text(
        json.dumps({"private_key_b64": local_priv, "public_key_b64": local_pub}) + "\n", encoding="utf-8"
    )
    rows.append({"pubkey_b64u": local_pub})
    for i in range(peers):
        _priv, pub = run_wrapper._deterministic_ed25519_keypair(f"{bundle_hash}:{i}")
        rows.append({"pubkey_b64u": pub})
    (cfg / "peer_registry_v1.json").write_text(json.dumps({"schema": "peer_registry_v1", "peers": rows}) + "\n", encoding="utf-8")


def _prepare_run(tmp_path: Path, bundle_id: str) -> Path:
    outdir = tmp_path / "run"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="linear",
        created_at_utc="2026-01-01T00:00:00Z",
        bundle_id=bundle_id,
    )
    return outdir


def _emit_reflection_and_graph(
    outdir: Path,
    *,
    graph_path: Path,
    recall_path: Path,
    task_plan_path: Path,
    memory_max_nodes: int = 0,
    memory_max_edges: int = 0,
) -> None:
    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir,
        telemetry={"run_id": outdir.name, "metrics": {"E": 0.1, "T": 0.2}},
        profile="reproducible_audit",
        reflection_mode="structured",
        memory_graph_mode="update",
        memory_graph_path=str(graph_path),
        memory_recall_mode="emit",
        memory_recall_path=str(recall_path),
        memory_max_nodes=memory_max_nodes,
        memory_max_edges=memory_max_edges,
        task_plan_mode="emit",
        task_plan_path=str(task_plan_path),
    )


def test_memory_graph_created_weighted_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "mg-created"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    graph_path = tmp_path / "out" / "cognition_memory_graph.json"

    _emit_reflection_and_graph(outdir, graph_path=graph_path, recall_path=tmp_path / "out" / "cognition_memory_recall.json", task_plan_path=tmp_path / "out" / "cognition_task_plan.json")
    assert graph_path.exists()

    schema = json.loads((ROOT / "schema" / "cognition_memory_graph_v1.schema.json").read_text(encoding="utf-8"))
    payload = json.loads(graph_path.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(payload)


def test_memory_graph_idempotent_on_repeat_same_trace(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "mg-idempotent"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    graph_path = tmp_path / "out" / "idempotent_graph.json"

    _emit_reflection_and_graph(outdir, graph_path=graph_path, recall_path=tmp_path / "out" / "cognition_memory_recall.json", task_plan_path=tmp_path / "out" / "cognition_task_plan.json")
    first = graph_path.read_bytes()
    _emit_reflection_and_graph(outdir, graph_path=graph_path, recall_path=tmp_path / "out" / "cognition_memory_recall.json", task_plan_path=tmp_path / "out" / "cognition_task_plan.json")
    second = graph_path.read_bytes()
    assert first == second


def test_memory_graph_deterministic_replay_given_same_input() -> None:
    trace = {
        "schema": "cognition_trace_v1",
        "bundle_hash": "a" * 64,
        "bundle_hash_source": "evidence_content",
        "profile": "reproducible_audit",
        "mode": "structured",
        "reflection_score": 0.1,
        "self_consistency_delta": 0.0,
        "correction_applied": False,
        "reasoning_depth_used": 3,
        "reflection_blocks": ["a", "b"],
        "invariants_checked": ["x"],
        "findings": ["f"],
        "recommendations": ["r"],
    }
    g1 = update_memory_graph(load_memory_graph(Path("/tmp/nonexistent-a.json")), trace)
    g2 = update_memory_graph(load_memory_graph(Path("/tmp/nonexistent-b.json")), trace)
    b1 = json.dumps(g1, sort_keys=True, indent=2).encode("utf-8")
    b2 = json.dumps(g2, sort_keys=True, indent=2).encode("utf-8")
    assert b1 == b2


def test_memory_graph_does_not_modify_governance_artifacts(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "mg-no-impact"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    baseline = {
        name: (outdir / name).read_bytes()
        for name in ["evidence_bundle.json", "consensus_summary.json", "attestations.json", "peer_attestations.json"]
    }
    graph_path = tmp_path / "out" / "impact_graph.json"
    _emit_reflection_and_graph(outdir, graph_path=graph_path, recall_path=tmp_path / "out" / "cognition_memory_recall.json", task_plan_path=tmp_path / "out" / "cognition_task_plan.json")

    for name, before in baseline.items():
        assert (outdir / name).read_bytes() == before


def test_witness_only_unaffected(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"witness_only"}\n', encoding="utf-8")

    outdir = tmp_path / "witness"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=1)

    graph_path = tmp_path / "out" / "witness_graph.json"
    recall_path = tmp_path / "out" / "witness_recall.json"
    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir,
        telemetry={"run_id": "witness"},
        profile="witness_only",
        reflection_mode="structured",
        memory_graph_mode="update",
        memory_graph_path=str(graph_path),
        memory_recall_mode="emit",
        memory_recall_path=str(recall_path),
        task_plan_mode="emit",
        task_plan_path=str(tmp_path / "out" / "witness_task_plan.json"),
    )
    assert not graph_path.exists()
    assert not recall_path.exists()
    assert not (tmp_path / "out" / "witness_task_plan.json").exists()


def test_memory_graph_corrupt_file_recovers_deterministically(tmp_path: Path) -> None:
    graph_path = tmp_path / "corrupt_graph.json"
    graph_path.write_text('{"schema":"cognition_memory_graph_v1","nodes":[', encoding="utf-8")

    trace = {
        "schema": "cognition_trace_v1",
        "bundle_hash": "b" * 64,
        "bundle_hash_source": "evidence_content",
        "profile": "reproducible_audit",
        "mode": "structured",
        "reflection_score": 0.2,
        "self_consistency_delta": 0.0,
        "correction_applied": False,
        "reasoning_depth_used": 3,
        "reflection_blocks": ["a"],
        "invariants_checked": ["x"],
        "findings": ["f"],
        "recommendations": ["r"],
    }

    recovered = update_memory_graph(load_memory_graph(graph_path), trace)
    write_memory_graph(graph_path, recovered)
    first = graph_path.read_bytes()

    recovered_again = update_memory_graph(load_memory_graph(graph_path), trace)
    write_memory_graph(graph_path, recovered_again)
    second = graph_path.read_bytes()

    assert first == second
    schema = json.loads((ROOT / "schema" / "cognition_memory_graph_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(json.loads(second.decode("utf-8")))


def test_memory_graph_pruning_deterministic() -> None:
    trace = {
        "schema": "cognition_trace_v1",
        "bundle_hash": "c" * 64,
        "bundle_hash_source": "evidence_content",
        "profile": "reproducible_audit",
        "mode": "structured",
        "reflection_score": 0.3,
        "self_consistency_delta": 0.0,
        "correction_applied": False,
        "reasoning_depth_used": 3,
        "reflection_blocks": ["a"],
        "invariants_checked": ["x"],
        "findings": ["f"],
        "recommendations": ["r"],
    }
    base_graph = {
        "schema": "cognition_memory_graph_v1",
        "nodes": [
            {"node_id": "n3", "kind": "misc", "label": "n3"},
            {"node_id": "n1", "kind": "misc", "label": "n1"},
            {"node_id": "n2", "kind": "misc", "label": "n2"},
        ],
        "edges": [
            {"edge_id": "e1", "source": "n1", "target": "n2", "relation": "r"},
        ],
        "bundle_hash_index": [],
    }

    g1 = update_memory_graph(base_graph, trace, max_nodes=4, max_edges=2)
    g2 = update_memory_graph(base_graph, trace, max_nodes=4, max_edges=2)
    assert json.dumps(g1, sort_keys=True, indent=2) == json.dumps(g2, sort_keys=True, indent=2)


def test_memory_graph_pruning_idempotent_under_repeat() -> None:
    trace = {
        "schema": "cognition_trace_v1",
        "bundle_hash": "d" * 64,
        "bundle_hash_source": "evidence_content",
        "profile": "reproducible_audit",
        "mode": "structured",
        "reflection_score": 0.4,
        "self_consistency_delta": 0.0,
        "correction_applied": False,
        "reasoning_depth_used": 3,
        "reflection_blocks": ["a"],
        "invariants_checked": ["x"],
        "findings": ["f"],
        "recommendations": ["r"],
    }
    graph = {
        "schema": "cognition_memory_graph_v1",
        "nodes": [{"node_id": f"n{i}", "kind": "misc", "label": f"n{i}"} for i in range(6)],
        "edges": [
            {"edge_id": "e1", "source": "n0", "target": "n1", "relation": "r"},
            {"edge_id": "e2", "source": "n1", "target": "n2", "relation": "r"},
            {"edge_id": "e3", "source": "n2", "target": "n3", "relation": "r"},
            {"edge_id": "e4", "source": "n3", "target": "n4", "relation": "r"},
        ],
        "bundle_hash_index": [],
    }

    once = update_memory_graph(graph, trace, max_nodes=4, max_edges=2)
    twice = update_memory_graph(once, trace, max_nodes=4, max_edges=2)
    assert json.dumps(once, sort_keys=True, indent=2) == json.dumps(twice, sort_keys=True, indent=2)


def test_cognition_flags_do_not_mutate_governance_bytes(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "mg-tripwire"
    _seed_weighted_env(tmp_path, bundle_id)

    # build separate runs deterministically
    out_off = _prepare_run(tmp_path / "off_env", bundle_id)
    out_on = _prepare_run(tmp_path / "on_env", bundle_id)

    baseline = {
        name: (out_off / name).read_bytes()
        for name in ["evidence_bundle.json", "consensus_summary.json", "attestations.json", "peer_attestations.json"]
    }

    _emit_reflection_and_graph(
        out_on,
        graph_path=tmp_path / "out" / "tripwire_graph.json",
        recall_path=tmp_path / "out" / "tripwire_recall.json",
        task_plan_path=tmp_path / "out" / "tripwire_task_plan.json",
        memory_max_nodes=8,
        memory_max_edges=8,
    )

    for name, before in baseline.items():
        assert (out_on / name).read_bytes() == before

    evidence = json.loads((out_on / "evidence_bundle.json").read_text(encoding="utf-8"))
    artifact_paths = sorted(str(a.get("path", "")) for a in evidence.get("artifacts", []) if isinstance(a, dict))
    assert all(not p.startswith("cognition_") for p in artifact_paths)
