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


def _emit_reflection_graph_recall(outdir: Path, *, graph_path: Path, recall_path: Path) -> None:
    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir,
        telemetry={"run_id": outdir.name, "metrics": {"E": 0.1, "T": 0.2}},
        profile="reproducible_audit",
        reflection_mode="structured",
        memory_graph_mode="update",
        memory_graph_path=str(graph_path),
        memory_recall_mode="emit",
        memory_recall_path=str(recall_path),
    )


def test_memory_recall_created_weighted_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "recall-created"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    graph_path = tmp_path / "out" / "cognition_memory_graph.json"
    recall_path = tmp_path / "out" / "cognition_memory_recall.json"

    _emit_reflection_graph_recall(outdir, graph_path=graph_path, recall_path=recall_path)
    assert recall_path.exists()



def test_memory_recall_deterministic_replay_byte_equal(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "recall-idempotent"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    graph_path = tmp_path / "out" / "idempotent_graph.json"
    recall_path = tmp_path / "out" / "idempotent_recall.json"

    _emit_reflection_graph_recall(outdir, graph_path=graph_path, recall_path=recall_path)
    first = recall_path.read_bytes()
    _emit_reflection_graph_recall(outdir, graph_path=graph_path, recall_path=recall_path)
    second = recall_path.read_bytes()
    assert first == second


def test_memory_recall_does_not_modify_governance_artifacts(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "recall-no-impact"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    baseline = {
        name: (outdir / name).read_bytes()
        for name in ["evidence_bundle.json", "consensus_summary.json", "attestations.json", "peer_attestations.json"]
    }
    graph_path = tmp_path / "out" / "impact_graph.json"
    recall_path = tmp_path / "out" / "impact_recall.json"

    _emit_reflection_graph_recall(outdir, graph_path=graph_path, recall_path=recall_path)

    for name, before in baseline.items():
        assert (outdir / name).read_bytes() == before


def test_memory_recall_witness_only_unaffected(monkeypatch, tmp_path: Path) -> None:
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
    )
    assert not graph_path.exists()
    assert not recall_path.exists()


def test_memory_recall_schema_validation(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "recall-schema"
    _seed_weighted_env(tmp_path, bundle_id)
    outdir = _prepare_run(tmp_path, bundle_id)
    graph_path = tmp_path / "out" / "schema_graph.json"
    recall_path = tmp_path / "out" / "schema_recall.json"

    _emit_reflection_graph_recall(outdir, graph_path=graph_path, recall_path=recall_path)

    schema = json.loads((ROOT / "schema" / "cognition_memory_recall_v1.schema.json").read_text(encoding="utf-8"))
    payload = json.loads(recall_path.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(payload)
