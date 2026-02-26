from __future__ import annotations

import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

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


def _emit_all_cognition(outdir: Path, *, graph_path: Path, recall_path: Path, task_plan_path: Path) -> None:
    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir,
        telemetry={"run_id": outdir.name, "metrics": {"E": 0.1, "T": 0.2}},
        profile="reproducible_audit",
        reflection_mode="structured",
        memory_graph_mode="update",
        memory_graph_path=str(graph_path),
        memory_recall_mode="emit",
        memory_recall_path=str(recall_path),
        task_plan_mode="emit",
        task_plan_path=str(task_plan_path),
    )


def test_task_plan_created_weighted_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    _seed_weighted_env(tmp_path, "task-plan-created")
    outdir = _prepare_run(tmp_path, "task-plan-created")

    task_plan_path = tmp_path / "out" / "cognition_task_plan.json"
    _emit_all_cognition(
        outdir,
        graph_path=tmp_path / "out" / "graph.json",
        recall_path=tmp_path / "out" / "recall.json",
        task_plan_path=task_plan_path,
    )
    assert task_plan_path.exists()


def test_task_plan_deterministic_replay_byte_equal(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    _seed_weighted_env(tmp_path, "task-plan-replay")
    outdir = _prepare_run(tmp_path, "task-plan-replay")

    graph_path = tmp_path / "out" / "replay_graph.json"
    recall_path = tmp_path / "out" / "replay_recall.json"
    task_plan_path = tmp_path / "out" / "replay_task_plan.json"

    _emit_all_cognition(outdir, graph_path=graph_path, recall_path=recall_path, task_plan_path=task_plan_path)
    first = task_plan_path.read_bytes()
    _emit_all_cognition(outdir, graph_path=graph_path, recall_path=recall_path, task_plan_path=task_plan_path)
    second = task_plan_path.read_bytes()
    assert first == second


def test_task_plan_schema_validation(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    _seed_weighted_env(tmp_path, "task-plan-schema")
    outdir = _prepare_run(tmp_path, "task-plan-schema")

    task_plan_path = tmp_path / "out" / "schema_task_plan.json"
    _emit_all_cognition(
        outdir,
        graph_path=tmp_path / "out" / "schema_graph.json",
        recall_path=tmp_path / "out" / "schema_recall.json",
        task_plan_path=task_plan_path,
    )

    schema = json.loads((ROOT / "schema" / "cognition_task_plan_v1.schema.json").read_text(encoding="utf-8"))
    payload = json.loads(task_plan_path.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(payload)


def test_task_plan_governance_non_impact(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    _seed_weighted_env(tmp_path, "task-plan-impact")
    outdir = _prepare_run(tmp_path, "task-plan-impact")
    baseline = {
        name: (outdir / name).read_bytes()
        for name in ["evidence_bundle.json", "consensus_summary.json", "attestations.json", "peer_attestations.json"]
    }

    _emit_all_cognition(
        outdir,
        graph_path=tmp_path / "out" / "impact_graph.json",
        recall_path=tmp_path / "out" / "impact_recall.json",
        task_plan_path=tmp_path / "out" / "impact_task_plan.json",
    )

    for name, before in baseline.items():
        assert (outdir / name).read_bytes() == before

    evidence_bundle = json.loads((outdir / "evidence_bundle.json").read_text(encoding="utf-8"))
    artifact_paths = [str(item.get("path") or "") for item in evidence_bundle.get("artifacts", [])]
    banned_tokens = ("cognition", "task_plan", "memory_graph", "memory_recall")
    assert all(not any(token in path for token in banned_tokens) for path in artifact_paths)


def test_task_plan_witness_unaffected(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"witness_only"}\n', encoding="utf-8")

    outdir = tmp_path / "witness"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=1)

    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir,
        telemetry={"run_id": "witness"},
        profile="witness_only",
        reflection_mode="structured",
        memory_graph_mode="update",
        memory_graph_path=str(tmp_path / "out" / "wg.json"),
        memory_recall_mode="emit",
        memory_recall_path=str(tmp_path / "out" / "wr.json"),
        task_plan_mode="emit",
        task_plan_path=str(tmp_path / "out" / "wt.json"),
    )

    assert not (outdir / "cognition_trace.json").exists()
    assert not (tmp_path / "out" / "wg.json").exists()
    assert not (tmp_path / "out" / "wr.json").exists()
    assert not (tmp_path / "out" / "wt.json").exists()




def test_task_plan_canonical_json_and_entropy_denylist(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    _seed_weighted_env(tmp_path, "task-plan-canonical")
    outdir = _prepare_run(tmp_path, "task-plan-canonical")

    task_plan_path = tmp_path / "out" / "canonical_task_plan.json"
    _emit_all_cognition(
        outdir,
        graph_path=tmp_path / "out" / "canonical_graph.json",
        recall_path=tmp_path / "out" / "canonical_recall.json",
        task_plan_path=task_plan_path,
    )

    raw = task_plan_path.read_bytes()
    assert raw.endswith(b"\n")
    assert b"\r\n" not in raw
    payload = json.loads(raw.decode("utf-8"))

    # canonical key ordering check
    canonical = json.dumps(payload, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    assert raw == canonical

    # stable IDs and ordering by numeric suffix
    task_ids = [task["task_id"] for task in payload["tasks"]]
    assert task_ids == sorted(task_ids)

    entropy_keys = {"created_at", "timestamp", "uuid", "nonce", "rand", "random"}

    def walk(obj):
        if isinstance(obj, dict):
            for k, v in obj.items():
                assert k not in entropy_keys
                walk(v)
        elif isinstance(obj, list):
            for item in obj:
                walk(item)

    walk(payload)


def test_task_plan_missing_gate_no_outputs(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    _seed_weighted_env(tmp_path, "task-plan-gates")
    outdir = _prepare_run(tmp_path, "task-plan-gates")

    graph_path = tmp_path / "out" / "g.json"
    recall_path = tmp_path / "out" / "r.json"
    task_plan_path = tmp_path / "out" / "t.json"
    cases = [
        dict(profile="reproducible_audit", reflection_mode="off", memory_graph_mode="update", memory_graph_path=str(graph_path), memory_recall_mode="emit", memory_recall_path=str(recall_path), task_plan_mode="emit", task_plan_path=str(task_plan_path)),
        dict(profile="witness_only", reflection_mode="structured", memory_graph_mode="update", memory_graph_path=str(graph_path), memory_recall_mode="emit", memory_recall_path=str(recall_path), task_plan_mode="emit", task_plan_path=str(task_plan_path)),
        dict(profile="reproducible_audit", reflection_mode="structured", memory_graph_mode="off", memory_graph_path=str(graph_path), memory_recall_mode="emit", memory_recall_path=str(recall_path), task_plan_mode="emit", task_plan_path=str(task_plan_path)),
        dict(profile="reproducible_audit", reflection_mode="structured", memory_graph_mode="update", memory_graph_path="", memory_recall_mode="emit", memory_recall_path=str(recall_path), task_plan_mode="emit", task_plan_path=str(task_plan_path)),
        dict(profile="reproducible_audit", reflection_mode="structured", memory_graph_mode="update", memory_graph_path=str(graph_path), memory_recall_mode="off", memory_recall_path=str(recall_path), task_plan_mode="emit", task_plan_path=str(task_plan_path)),
        dict(profile="reproducible_audit", reflection_mode="structured", memory_graph_mode="update", memory_graph_path=str(graph_path), memory_recall_mode="emit", memory_recall_path="", task_plan_mode="emit", task_plan_path=str(task_plan_path)),
        dict(profile="reproducible_audit", reflection_mode="structured", memory_graph_mode="update", memory_graph_path=str(graph_path), memory_recall_mode="emit", memory_recall_path=str(recall_path), task_plan_mode="off", task_plan_path=str(task_plan_path)),
        dict(profile="reproducible_audit", reflection_mode="structured", memory_graph_mode="update", memory_graph_path=str(graph_path), memory_recall_mode="emit", memory_recall_path=str(recall_path), task_plan_mode="emit", task_plan_path=""),
    ]

    for case in cases:
        for p in [outdir / "cognition_trace.json", graph_path, recall_path, task_plan_path]:
            if p.exists():
                p.unlink()
        run_wrapper._maybe_emit_cognition_outputs(outdir=outdir, telemetry={"run_id": "gates"}, **case)
        assert not (outdir / "cognition_trace.json").exists()
        assert not graph_path.exists()
        assert not recall_path.exists()
        assert not task_plan_path.exists()
