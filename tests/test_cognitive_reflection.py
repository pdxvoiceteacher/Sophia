from __future__ import annotations

import json
from pathlib import Path

from tools.cognition.reflection_engine import build_cognition_trace, write_cognition_trace
from tools.telemetry import run_wrapper


def _seed_weighted_env(tmp_path: Path, bundle_id: str, peers: int = 2) -> None:
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")
    bundle_hash = __import__("hashlib").sha256(bundle_id.encode("utf-8")).hexdigest()
    rows = []
    local_priv, local_pub = run_wrapper._deterministic_ed25519_keypair("local-attestation-seed")
    (cfg / "local_attestation_key.json").write_text(
        json.dumps({"private_key_b64": local_priv, "public_key_b64": local_pub}) + "\n", encoding="utf-8"
    )
    rows.append({"pubkey_b64u": local_pub})
    for i in range(peers):
        _priv, pub = run_wrapper._deterministic_ed25519_keypair(f"{bundle_hash}:{i}")
        rows.append({"pubkey_b64u": pub})
    (cfg / "peer_registry_v1.json").write_text(json.dumps({"schema": "peer_registry_v1", "peers": rows}) + "\n", encoding="utf-8")


def test_reflection_produces_trace_file(tmp_path: Path) -> None:
    telemetry = {"metrics": {"E": 0.5, "T": 0.8}, "run_id": "r1"}
    outdir = tmp_path / "out"
    outdir.mkdir(parents=True, exist_ok=True)
    out = write_cognition_trace(outdir=outdir, telemetry=telemetry, mode="structured")
    assert out is not None
    trace = json.loads((outdir / "cognition_trace.json").read_text(encoding="utf-8"))
    assert trace["reflection_enabled"] is True
    assert isinstance(trace["reflection_score"], float)


def test_reflection_does_not_modify_consensus_json(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    bundle_id = "cognition-consensus-stable"
    _seed_weighted_env(tmp_path, bundle_id, peers=2)

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
    before = (outdir / "consensus_summary.json").read_bytes()
    write_cognition_trace(
        outdir=outdir,
        telemetry={"run_id": outdir.name, "metrics": {"E": 0.1, "T": 0.2}},
        mode="structured",
    )
    after = (outdir / "consensus_summary.json").read_bytes()
    assert before == after


def test_reflection_deterministic_replay(tmp_path: Path) -> None:
    telemetry = {"run_id": "repeat", "metrics": {"Lambda": 0.3, "DeltaS": 0.1}}
    t1 = build_cognition_trace(telemetry=telemetry, mode="structured")
    t2 = build_cognition_trace(telemetry=telemetry, mode="structured")
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

    # reflection off path returns no output file and witness consensus remains v1.
    out = write_cognition_trace(outdir=outdir, telemetry={"run_id": "witness"}, mode="off")
    assert out is None
    assert not (outdir / "cognition_trace.json").exists()
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"
