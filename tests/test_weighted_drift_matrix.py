from __future__ import annotations

import json
from pathlib import Path

from tools.telemetry import run_wrapper


def _prepare(tmp_path: Path, profile: str, policy: dict | None = None) -> tuple[Path, list[dict[str, str]]]:
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text(json.dumps({"profile": profile}) + "\n", encoding="utf-8")
    if policy is not None:
        (cfg / "policy_thresholds.json").write_text(json.dumps(policy) + "\n", encoding="utf-8")

    outdir = tmp_path / "run"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    return outdir, artifacts


def test_weighted_drift_matrix_pass_threshold_convergent(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    policy = {
        "network_profile": "reproducible_audit",
        "consensus_requirements": {
            "min_total_attestations": 4,
            "min_weighted_pass": 4.0,
            "max_weighted_fail": 10.0,
            "block_on_any_fail": False,
            "allow_pending_to_satisfy": False,
        },
        "export_policy": {"require_convergent": True, "require_attestations": True, "allowed_formats": ["json"]},
    }
    outdir, artifacts = _prepare(tmp_path, "reproducible_audit", policy)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=3, simulate_peer_weight_mode="linear")
    c = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert c["schema"] == "consensus_summary_v2"
    assert c["consensus"] == "convergent"


def test_weighted_drift_matrix_fail_threshold_divergent(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    policy = {
        "network_profile": "reproducible_audit",
        "consensus_requirements": {
            "min_total_attestations": 4,
            "min_weighted_pass": 3.0,
            "max_weighted_fail": 1.0,
            "block_on_any_fail": False,
            "allow_pending_to_satisfy": False,
        },
        "export_policy": {"require_convergent": True, "require_attestations": True, "allowed_formats": ["json"]},
    }
    outdir, artifacts = _prepare(tmp_path, "reproducible_audit", policy)
    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=6,
        simulate_peer_weight_mode="adversarial",
        adversarial_weight_pattern="minority_high_weight_fail",
    )
    c = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert c["consensus"] == "divergent"


def test_weighted_drift_matrix_central_fail_always_divergent(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir, artifacts = _prepare(tmp_path, "reproducible_audit", None)

    def fake_status(item: dict) -> str:
        if isinstance(item, dict) and item.get("simulated"):
            return "pass"
        return "fail"

    monkeypatch.setattr(run_wrapper, "_status_from_signed_attestation", fake_status)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=5, simulate_peer_weight_mode="linear")
    c = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert c["central"]["pass"] == 0
    assert c["consensus"] == "divergent"


def test_weighted_drift_matrix_borderline_threshold_deterministic(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    policy = {
        "network_profile": "reproducible_audit",
        "consensus_requirements": {
            "min_total_attestations": 5,
            "min_weighted_pass": 4.0,
            "max_weighted_fail": 1.0,
            "block_on_any_fail": False,
            "allow_pending_to_satisfy": False,
        },
        "export_policy": {"require_convergent": True, "require_attestations": True, "allowed_formats": ["json"]},
    }
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text(json.dumps({"profile": "reproducible_audit"}) + "\n", encoding="utf-8")
    (cfg / "policy_thresholds.json").write_text(json.dumps(policy) + "\n", encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    for name in ["a", "b"]:
        outdir = tmp_path / name
        (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
        (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
        run_wrapper._write_evidence_and_consensus(
            outdir,
            artifacts,
            simulate_peers=5,
            simulate_peer_weight_mode="adversarial",
            adversarial_weight_pattern="borderline_threshold_case",
            created_at_utc="2026-01-01T00:00:00Z",
            bundle_id="borderline-drift",
        )

    assert (tmp_path / "a" / "consensus_summary.json").read_bytes() == (tmp_path / "b" / "consensus_summary.json").read_bytes()
