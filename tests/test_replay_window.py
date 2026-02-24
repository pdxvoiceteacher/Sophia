from __future__ import annotations

import json
from pathlib import Path

from tools.security.swarm_crypto import is_attestation_expired, is_within_replay_window
from tools.telemetry import run_wrapper


def test_replay_window_helpers_deterministic() -> None:
    assert is_within_replay_window(
        created_at_utc="2026-01-01T00:00:00Z",
        reference_utc="2026-01-01T00:00:05Z",
        replay_window_s=10,
    )
    assert not is_within_replay_window(
        created_at_utc="2026-01-01T00:00:00Z",
        reference_utc="2026-01-01T00:00:20Z",
        replay_window_s=10,
    )
    assert not is_attestation_expired(
        created_at_utc="2026-01-01T00:00:00Z",
        reference_utc="2026-01-01T00:00:05Z",
        ttl_s=10,
    )
    assert is_attestation_expired(
        created_at_utc="2026-01-01T00:00:00Z",
        reference_utc="2026-01-01T00:00:20Z",
        ttl_s=10,
    )


def test_weighted_profile_replay_scaffold_fields_present(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    outdir = tmp_path / "weighted-replay"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="adversarial",
        replay_window_s=60,
        attestation_ttl_s=60,
        created_at_utc="2026-01-01T00:00:00Z",
        bundle_id="b2-4-replay",
    )
    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all("replay_window_ok" in p for p in peers)
    assert all("attestation_expired" in p for p in peers)
    assert all(p["replay_window_ok"] is True for p in peers)
    assert all(p["attestation_expired"] is False for p in peers)


def test_witness_only_replay_scaffold_not_emitted(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "witness-replay"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="adversarial",
        replay_window_s=60,
        attestation_ttl_s=60,
    )
    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all("replay_window_ok" not in p for p in peers)
    assert all("attestation_expired" not in p for p in peers)


def test_replay_expiry_metadata_never_appears_under_witness_only_even_with_patterns(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "witness-never-metadata"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=3,
        simulate_peer_weight_mode="adversarial",
        adversarial_weight_pattern="borderline_threshold_case",
        replay_window_s=120,
        attestation_ttl_s=120,
    )
    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all("replay_window_ok" not in p and "attestation_expired" not in p for p in peers)

