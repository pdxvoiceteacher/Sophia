from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.telemetry import run_wrapper


def _prep_out(tmp_path: Path, name: str) -> tuple[Path, list[dict[str, str]]]:
    outdir = tmp_path / name
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    return outdir, artifacts


def test_witness_only_emits_consensus_summary_v1(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir, artifacts = _prep_out(tmp_path, "w1")
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2)
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"


def test_no_path_b_fields_appear_in_v1_output(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir, artifacts = _prep_out(tmp_path, "w2")
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="linear")
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert "bundle_hash_source" not in consensus["policy_gate"]
    assert "peer_weight_mode" not in consensus["policy_gate"]


def test_central_pass_required_for_convergence(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir, artifacts = _prep_out(tmp_path, "w3")

    def fake_status(item: dict) -> str:
        if isinstance(item, dict) and item.get("simulated") is True:
            return "pass"
        return "fail"

    monkeypatch.setattr(run_wrapper, "_status_from_signed_attestation", fake_status)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=3)
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["central"]["pass"] == 0
    assert consensus["consensus"] != "convergent"


def test_weighted_flags_ignored_in_witness_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir, artifacts = _prep_out(tmp_path, "w4")
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=4, simulate_peer_weight_mode="adversarial")
    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert all(float(item.get("simulated_weight", 0.0)) == 1.0 for item in peers)
    assert all((item.get("payload") or {}).get("results", {}).get("status") == "pass" for item in peers)


def test_deterministic_freeze_verifier_passes() -> None:
    result = subprocess.run(
        [sys.executable, "scripts/verify_secure_swarm_freeze.py", "--repo-root", ".", "--out-root", "out/freeze_invariants"],
        capture_output=True,
        text=True,
        check=True,
    )
    assert "[freeze_verify] OK deterministic peer_attestations and consensus schema validation" in result.stdout
