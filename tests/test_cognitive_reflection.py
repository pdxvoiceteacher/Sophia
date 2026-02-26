from __future__ import annotations

import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.cognition.reflection_engine import build_cognition_trace, write_cognition_trace
from tools.telemetry import run_wrapper


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


def _prepare_run(outdir: Path, *, bundle_id: str, created_at: str = "2026-01-01T00:00:00Z") -> None:
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="linear",
        created_at_utc=created_at,
        bundle_id=bundle_id,
    )


def _emit_structured_trace(outdir: Path, telemetry: dict[str, object]) -> None:
    evidence = json.loads((outdir / "evidence_bundle.json").read_text(encoding="utf-8"))
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    source = str(((consensus.get("policy_gate") or {}).get("bundle_hash_source") or "evidence_content"))
    out = write_cognition_trace(
        outdir=outdir,
        telemetry=telemetry,
        mode="structured",
        profile="reproducible_audit",
        bundle_hash=str(evidence["bundle_sha256"]),
        bundle_hash_source=source,
    )
    assert out is not None


def test_reflection_produces_trace_file(tmp_path: Path) -> None:
    telemetry = {"metrics": {"E": 0.5, "T": 0.8}, "run_id": "r1"}
    outdir = tmp_path / "out"
    outdir.mkdir(parents=True, exist_ok=True)
    out = write_cognition_trace(
        outdir=outdir,
        telemetry=telemetry,
        mode="structured",
        profile="reproducible_audit",
        bundle_hash="a" * 64,
        bundle_hash_source="evidence_content",
    )
    assert out is not None
    trace = json.loads((outdir / "cognition_trace.json").read_text(encoding="utf-8"))
    assert trace["schema"] == "cognition_trace_v1"
    assert trace["mode"] == "structured"


def test_reflection_trace_validates_schema(tmp_path: Path) -> None:
    schema = json.loads((Path(__file__).resolve().parents[1] / "schema" / "cognition_trace_v1.schema.json").read_text(encoding="utf-8"))
    outdir = tmp_path / "schema-check"
    outdir.mkdir(parents=True, exist_ok=True)
    write_cognition_trace(
        outdir=outdir,
        telemetry={"run_id": "schema-check", "metrics": {"x": 1}},
        mode="structured",
        profile="reproducible_audit",
        bundle_hash="b" * 64,
        bundle_hash_source="bundle_id_override",
    )
    payload = json.loads((outdir / "cognition_trace.json").read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(payload)


def test_reflection_does_not_modify_consensus_json(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "cognition-consensus-stable"
    _seed_weighted_env(tmp_path, bundle_id, peers=2)

    out_off = tmp_path / "off"
    out_on = tmp_path / "on"
    _prepare_run(out_off, bundle_id=bundle_id)
    _prepare_run(out_on, bundle_id=bundle_id)

    _emit_structured_trace(out_on, telemetry={"run_id": "on", "metrics": {"E": 0.1, "T": 0.2}})

    for name in ["evidence_bundle.json", "consensus_summary.json", "attestations.json", "peer_attestations.json"]:
        assert (out_off / name).read_bytes() == (out_on / name).read_bytes()


def test_reflection_deterministic_replay(tmp_path: Path) -> None:
    telemetry = {"run_id": "repeat", "metrics": {"Lambda": 0.3, "DeltaS": 0.1}}
    t1 = build_cognition_trace(
        telemetry=telemetry,
        mode="structured",
        profile="reproducible_audit",
        bundle_hash="c" * 64,
        bundle_hash_source="evidence_content",
    )
    t2 = build_cognition_trace(
        telemetry=telemetry,
        mode="structured",
        profile="reproducible_audit",
        bundle_hash="c" * 64,
        bundle_hash_source="evidence_content",
    )
    assert t1 == t2


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

    out = write_cognition_trace(
        outdir=outdir,
        telemetry={"run_id": "witness"},
        mode="off",
        profile="witness_only",
        bundle_hash="d" * 64,
        bundle_hash_source="evidence_content",
    )
    assert out is None
    assert not (outdir / "cognition_trace.json").exists()
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"


def test_run_wrapper_cognition_trace_requires_full_gating(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "trace-gating"
    _seed_weighted_env(tmp_path, bundle_id, peers=2)

    outdir = tmp_path / "run"
    _prepare_run(outdir, bundle_id=bundle_id)

    # Full gates satisfied -> trace/graph/recall present
    graph_path = tmp_path / "out" / "trace_gate_graph.json"
    recall_path = tmp_path / "out" / "trace_gate_recall.json"
    task_plan_path = tmp_path / "out" / "trace_gate_task_plan.json"
    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir,
        telemetry={"run_id": "trace-gating", "metrics": {"E": 0.1, "T": 0.2}},
        profile="reproducible_audit",
        reflection_mode="structured",
        memory_graph_mode="update",
        memory_graph_path=str(graph_path),
        memory_recall_mode="emit",
        memory_recall_path=str(recall_path),
        task_plan_mode="emit",
        task_plan_path=str(task_plan_path),
    )
    assert (outdir / "cognition_trace.json").exists()
    assert graph_path.exists()
    assert recall_path.exists()
    assert task_plan_path.exists()

    # Remove one gate (reflection mode) -> no cognition outputs
    outdir2 = tmp_path / "run2"
    _prepare_run(outdir2, bundle_id=bundle_id)
    graph_path2 = tmp_path / "out" / "trace_gate_graph2.json"
    recall_path2 = tmp_path / "out" / "trace_gate_recall2.json"
    run_wrapper._maybe_emit_cognition_outputs(
        outdir=outdir2,
        telemetry={"run_id": "trace-gating-2", "metrics": {"E": 0.1, "T": 0.2}},
        profile="reproducible_audit",
        reflection_mode="off",
        memory_graph_mode="update",
        memory_graph_path=str(graph_path2),
        memory_recall_mode="emit",
        memory_recall_path=str(recall_path2),
    )
    assert not (outdir2 / "cognition_trace.json").exists()
    assert not graph_path2.exists()
    assert not recall_path2.exists()
