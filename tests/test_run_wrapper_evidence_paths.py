from __future__ import annotations

import json
import hashlib
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.telemetry import run_wrapper


def _seed_trusted_simulated_peers(tmp_path: Path, bundle_id: str, count: int, *, include_local: bool = True) -> None:
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    bundle_hash = hashlib.sha256(bundle_id.encode("utf-8")).hexdigest()
    peers: list[dict[str, str]] = []
    if include_local:
        local_priv, local_pub = run_wrapper._deterministic_ed25519_keypair("local-attestation-seed")
        (cfg / "local_attestation_key.json").write_text(
            json.dumps({"private_key_b64": local_priv, "public_key_b64": local_pub}) + "\n",
            encoding="utf-8",
        )
        peers.append({"pubkey_b64u": local_pub})
    for i in range(count):
        _priv, pub = run_wrapper._deterministic_ed25519_keypair(f"{bundle_hash}:{i}")
        peers.append({"pubkey_b64u": pub})
    (cfg / "peer_registry_v1.json").write_text(json.dumps({"schema": "peer_registry_v1", "peers": peers}) + "\n", encoding="utf-8")


def test_write_evidence_and_consensus_uses_outdir_relative_artifacts(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "portable-output"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    (outdir / "ucc_cov_out").mkdir(parents=True, exist_ok=True)
    (outdir / "ucc_cov_out" / "audit_bundle.json").write_text('{"metrics": {}}\n', encoding="utf-8")

    artifacts = [
        {"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64},
        {"path": "ucc_cov_out/audit_bundle.json", "sha256": "b" * 64},
    ]

    run_wrapper._write_evidence_and_consensus(outdir, artifacts)

    evidence = json.loads((outdir / "evidence_bundle.json").read_text(encoding="utf-8"))
    entries = {item["path"]: item for item in evidence["artifacts"]}

    assert "konomi_smoke_base/konomi_smoke_summary.json" in entries
    assert entries["konomi_smoke_base/konomi_smoke_summary.json"]["size_bytes"] > 0
    assert "ucc_cov_out/audit_bundle.json" in entries
    assert entries["ucc_cov_out/audit_bundle.json"]["size_bytes"] > 0


def test_emit_tel_events_flag_persists_after_preparse(tmp_path: Path) -> None:
    outdir = tmp_path / "out"
    cmd = [
        sys.executable,
        "-c",
        (
            "import sys;"
            "sys.argv=['run_wrapper.py','--out','" + str(outdir).replace('\\','/') + "','--emit-tel-events'];"
            "import tools.telemetry.run_wrapper as rw;"
            "print('1' if rw._TEL_EVENTS_EMIT else '0')"
        ),
    ]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert result.stdout.strip().endswith("1")


def test_emit_tel_events_touches_file_from_ucc_env_when_out_not_in_argv(tmp_path: Path) -> None:
    outdir = tmp_path / "env-out"
    ucc_file = outdir / "ucc_tel_events.jsonl"
    cmd = [
        sys.executable,
        "-c",
        (
            "import os,sys;"
            "os.environ['UCC_TEL_EVENTS_OUT']='" + str(ucc_file).replace('\\','/') + "';"
            "sys.argv=['run_wrapper.py','--emit-tel-events'];"
            "import tools.telemetry.run_wrapper"
        ),
    ]
    subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert (outdir / "tel_events.jsonl").exists()


def test_emit_tel_events_touch_does_not_truncate_existing_file(tmp_path: Path) -> None:
    outdir = tmp_path / "touch-out"
    outdir.mkdir(parents=True, exist_ok=True)
    tel_file = outdir / "tel_events.jsonl"
    tel_file.write_text('{\"preexisting\":true}\n', encoding="utf-8")
    cmd = [
        sys.executable,
        "-c",
        (
            "import sys;"
            "sys.argv=['run_wrapper.py','--out','" + str(outdir).replace('\\','/') + "','--emit-tel-events'];"
            "import tools.telemetry.run_wrapper"
        ),
    ]
    subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert tel_file.read_text(encoding="utf-8") == '{"preexisting":true}\n'


def test_emit_tel_events_accepts_ucc_env_directory(tmp_path: Path) -> None:
    outdir = tmp_path / "env-dir-out"
    cmd = [
        sys.executable,
        "-c",
        (
            "import os,sys;"
            "os.environ['UCC_TEL_EVENTS_OUT']='" + str(outdir).replace('\\','/') + "';"
            "sys.argv=['run_wrapper.py','--emit-tel-events'];"
            "import tools.telemetry.run_wrapper"
        ),
    ]
    subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert (outdir / "tel_events.jsonl").exists()


def test_write_evidence_emits_central_attestation_and_convergent_consensus(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "central"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    f = outdir / "konomi_smoke_base" / "konomi_smoke_summary.json"
    f.write_text('{\"ok\": true}\n', encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(outdir, artifacts)

    assert (outdir / "attestations.json").exists()
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["inputs"]["central_attestations_present"] is True
    assert consensus["consensus"] == "convergent"


def test_simulate_peers_emits_peer_attestations_and_counts(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "peers"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    f = outdir / "konomi_smoke_base" / "konomi_smoke_summary.json"
    f.write_text('{\"ok\": true}\n', encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2)

    peers_doc = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8"))
    assert len(peers_doc.get("attestations") or []) == 2
    assert all(item.get("simulated") is True for item in (peers_doc.get("attestations") or []))
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["peers"]["total"] == 2
    assert consensus["peers"]["pass"] == 2
    assert consensus["consensus"] == "convergent"


def test_preparse_does_not_mutate_sys_argv(tmp_path: Path) -> None:
    outdir = tmp_path / "argv-out"
    cmd = [
        sys.executable,
        "-c",
        (
            "import sys;"
            "sys.argv=['run_wrapper.py','--out','" + str(outdir).replace('\\','/') + "','--emit-tel','--emit-tel-events'];"
            "import tools.telemetry.run_wrapper as rw;"
            "print(' '.join(sys.argv));"
            "print('1' if rw._TEL_EMIT else '0');"
            "print('1' if rw._TEL_EVENTS_EMIT else '0')"
        ),
    ]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    lines = [ln.strip() for ln in result.stdout.splitlines() if ln.strip()]
    assert "--emit-tel" in lines[0]
    assert "--emit-tel-events" in lines[0]
    assert lines[-2] == "1"
    assert lines[-1] == "1"


def test_consensus_summary_emitted_by_wrapper_validates_schema(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "schema-check"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    f = outdir / "konomi_smoke_base" / "konomi_smoke_summary.json"
    f.write_text('{"ok": true}\n', encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=1)

    report = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    schema = json.loads((Path(__file__).resolve().parents[1] / "schema" / "consensus_summary_v1.schema.json").read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(report)


def test_simulated_peer_attestations_are_byte_identical_in_deterministic_mode(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    out_a = tmp_path / "det-a"
    out_b = tmp_path / "det-b"
    for outdir in [out_a, out_b]:
        (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
        (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    kwargs = {"simulate_peers": 2, "created_at_utc": "2026-01-01T00:00:00Z", "bundle_id": "bundle-fixed"}
    run_wrapper._write_evidence_and_consensus(out_a, artifacts, **kwargs)
    run_wrapper._write_evidence_and_consensus(out_b, artifacts, **kwargs)

    assert (out_a / "peer_attestations.json").read_bytes() == (out_b / "peer_attestations.json").read_bytes()


def test_bundle_id_override_stabilizes_peer_attestations_across_different_artifact_hashes(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    out_a = tmp_path / "ovr-a"
    out_b = tmp_path / "ovr-b"
    for outdir in [out_a, out_b]:
        (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
        (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")

    artifacts_a = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    artifacts_b = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "b" * 64}]
    kwargs = {"simulate_peers": 2, "created_at_utc": "2026-01-01T00:00:00Z", "bundle_id": "bundle-fixed"}
    run_wrapper._write_evidence_and_consensus(out_a, artifacts_a, **kwargs)
    run_wrapper._write_evidence_and_consensus(out_b, artifacts_b, **kwargs)

    assert (out_a / "peer_attestations.json").read_bytes() == (out_b / "peer_attestations.json").read_bytes()


def test_simulate_peers_linear_weight_mode_updates_weighted_counts(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "weighted"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")
    bundle_id = "weighted-linear-trusted"
    bundle_hash = hashlib.sha256(bundle_id.encode("utf-8")).hexdigest()
    peers = []
    for i in range(2):
        _priv, pub = run_wrapper._deterministic_ed25519_keypair(f"{bundle_hash}:{i}")
        peers.append({"pubkey_b64u": pub})
    (cfg / "peer_registry_v1.json").write_text(json.dumps({"schema": "peer_registry_v1", "peers": peers}) + "\n", encoding="utf-8")

    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="linear", bundle_id=bundle_id)

    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v2"
    assert consensus["peers"]["weighted_pass"] == 3.0
    assert consensus["policy_gate"]["peer_weight_mode"] == "linear"


def test_witness_only_emits_consensus_v1_without_path_b_fields(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "witness"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=1, bundle_id="bundle-fixed")

    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"
    assert "bundle_hash_source" not in consensus["policy_gate"]
    assert "peer_weight_mode" not in consensus["policy_gate"]


def test_central_dominance_blocks_convergent_without_central_pass(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "central-dominance"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    original = run_wrapper._status_from_signed_attestation

    def fake_status(item: dict) -> str:
        if isinstance(item, dict) and item.get("simulated") is True:
            return "pass"
        return "fail"

    monkeypatch.setattr(run_wrapper, "_status_from_signed_attestation", fake_status)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=3)
    monkeypatch.setattr(run_wrapper, "_status_from_signed_attestation", original)

    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["central"]["pass"] == 0
    assert consensus["peers"]["pass"] == 3
    assert consensus["consensus"] != "convergent"
    assert consensus["policy_gate"]["satisfied"] is False


def test_witness_only_cannot_emit_v2(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "witness-cannot-v2"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="linear")
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"


def test_central_pass_with_weighted_majority_fail_is_divergent(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    outdir = tmp_path / "weighted-majority-fail"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    def fake_status(item: dict) -> str:
        if isinstance(item, dict) and item.get("simulated") is True:
            return "fail"
        return "pass"

    monkeypatch.setattr(run_wrapper, "_status_from_signed_attestation", fake_status)
    bundle_id = "weighted-majority-fail"
    _seed_trusted_simulated_peers(tmp_path, bundle_id, 3)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=3, simulate_peer_weight_mode="linear", bundle_id=bundle_id)
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["consensus"] == "divergent"


def test_central_pass_borderline_weighted_threshold_is_deterministic(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")
    (cfg / "policy_thresholds.json").write_text(
        json.dumps(
            {
                "network_profile": "reproducible_audit",
                "consensus_requirements": {
                    "min_total_attestations": 3,
                    "min_weighted_pass": 3.0,
                    "max_weighted_fail": 1.0,
                    "block_on_any_fail": False,
                    "allow_pending_to_satisfy": False,
                },
                "export_policy": {"require_convergent": True, "require_attestations": True, "allowed_formats": ["json"]},
            }
        )
        + "\n",
        encoding="utf-8",
    )

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    for d in [tmp_path / "t1", tmp_path / "t2"]:
        (d / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
        (d / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
        run_wrapper._write_evidence_and_consensus(
            d,
            artifacts,
            simulate_peers=2,
            simulate_peer_weight_mode="linear",
            created_at_utc="2026-01-01T00:00:00Z",
            bundle_id="borderline-fixed",
        )

    c1 = (tmp_path / "t1" / "consensus_summary.json").read_bytes()
    c2 = (tmp_path / "t2" / "consensus_summary.json").read_bytes()
    assert c1 == c2


def test_weighted_profile_deterministic_replay(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]
    for d in [tmp_path / "r1", tmp_path / "r2"]:
        (d / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
        (d / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
        run_wrapper._write_evidence_and_consensus(
            d,
            artifacts,
            simulate_peers=5,
            simulate_peer_weight_mode="adversarial",
            created_at_utc="2026-01-01T00:00:00Z",
            bundle_id="pathb-replay",
        )

    assert (tmp_path / "r1" / "peer_attestations.json").read_bytes() == (tmp_path / "r2" / "peer_attestations.json").read_bytes()
    assert (tmp_path / "r1" / "consensus_summary.json").read_bytes() == (tmp_path / "r2" / "consensus_summary.json").read_bytes()


def test_adversarial_weight_distribution_math(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    outdir = tmp_path / "adversarial"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    bundle_id = "adversarial-weight-math"
    _seed_trusted_simulated_peers(tmp_path, bundle_id, 6)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=6, simulate_peer_weight_mode="adversarial", bundle_id=bundle_id)
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["peers"]["fail"] >= 1
    assert consensus["peers"]["weighted_fail"] > consensus["peers"]["weighted_pass"] / 3
    assert consensus["consensus"] == "divergent"


def test_weighted_profiles_require_explicit_weight_mode(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    monkeypatch.setattr(sys, "argv", ["run_wrapper.py", "--out", str(tmp_path / "o")])
    try:
        run_wrapper.main()
        assert False, "expected SystemExit when weight mode not explicit"
    except SystemExit as exc:
        assert "explicit --simulate-peer-weight-mode" in str(exc)


def test_profile_witness_only_emits_v1_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "profile-witness"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="adversarial")
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"


def test_profile_reproducible_audit_emits_v2_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    outdir = tmp_path / "profile-repro"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="linear")
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v2"


def test_profile_full_relay_emits_v2_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"full_relay"}\n', encoding="utf-8")

    outdir = tmp_path / "profile-full"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="adversarial")
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v2"


def test_witness_only_central_fail_blocks_even_with_weighted_majority(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    outdir = tmp_path / "witness-central-block"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    def fake_status(item: dict) -> str:
        if isinstance(item, dict) and item.get("simulated") is True:
            return "pass"
        return "fail"

    monkeypatch.setattr(run_wrapper, "_status_from_signed_attestation", fake_status)
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=5, simulate_peer_weight_mode="linear")
    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"
    assert consensus["peers"]["pass"] == 5
    assert consensus["central"]["pass"] == 0
    assert consensus["consensus"] != "convergent"



def test_witness_only_central_fail_blocks_even_with_weighted_majority_under_witness_only(monkeypatch, tmp_path: Path) -> None:
    test_witness_only_central_fail_blocks_even_with_weighted_majority(monkeypatch, tmp_path)


def test_key_id_emitted_under_weighted_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")

    outdir = tmp_path / "weighted-key-id"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="linear",
        created_at_utc="2026-01-01T00:00:00Z",
        bundle_id="weighted-key-id",
    )

    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all(isinstance((p.get("payload") or {}).get("key_id"), str) and (p.get("payload") or {}).get("key_id") for p in peers)
    assert all(p.get("key_validation_ok") is False for p in peers)


def test_key_id_not_emitted_under_witness_only(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)

    outdir = tmp_path / "witness-no-key-id"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="linear",
        created_at_utc="2026-01-01T00:00:00Z",
        bundle_id="witness-no-key-id",
    )

    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all("key_id" not in (p.get("payload") or {}) for p in peers)


def test_unknown_key_rejected_under_weighted(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)
    cfg = tmp_path / "config"
    cfg.mkdir(parents=True, exist_ok=True)
    (cfg / "network_policy_v1.json").write_text('{"profile":"reproducible_audit"}\n', encoding="utf-8")
    (cfg / "peer_registry_v1.json").write_text('{"schema":"peer_registry_v1","peers":[]}\n', encoding="utf-8")

    outdir = tmp_path / "weighted-unknown-key"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=3,
        simulate_peer_weight_mode="linear",
        created_at_utc="2026-01-01T00:00:00Z",
        bundle_id="weighted-unknown-key",
    )

    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all(p.get("key_enforced") is True for p in peers)
    assert all(p.get("key_validation_ok") is False for p in peers)
    assert all(p.get("attestation_valid") is False for p in peers)

    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v2"
    assert consensus["peers"]["weighted_pass"] == 0.0
    assert consensus["peers"]["pass"] == 0


def test_witness_only_ignores_key_enforcement(monkeypatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run_wrapper, "REPO", tmp_path)

    outdir = tmp_path / "witness-ignores-key-enforcement"
    (outdir / "konomi_smoke_base").mkdir(parents=True, exist_ok=True)
    (outdir / "konomi_smoke_base" / "konomi_smoke_summary.json").write_text('{"ok": true}\n', encoding="utf-8")
    artifacts = [{"path": "konomi_smoke_base/konomi_smoke_summary.json", "sha256": "a" * 64}]

    run_wrapper._write_evidence_and_consensus(
        outdir,
        artifacts,
        simulate_peers=2,
        simulate_peer_weight_mode="linear",
        created_at_utc="2026-01-01T00:00:00Z",
        bundle_id="witness-ignores-key-enforcement",
    )

    peers = json.loads((outdir / "peer_attestations.json").read_text(encoding="utf-8")).get("attestations") or []
    assert peers
    assert all("key_enforced" not in p for p in peers)
    assert all("attestation_valid" not in p for p in peers)

    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["schema"] == "consensus_summary_v1"
    assert consensus["peers"]["pass"] == 2
