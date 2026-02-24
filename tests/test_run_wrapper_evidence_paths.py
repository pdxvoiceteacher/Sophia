from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.telemetry import run_wrapper


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
    run_wrapper._write_evidence_and_consensus(outdir, artifacts, simulate_peers=2, simulate_peer_weight_mode="linear")

    consensus = json.loads((outdir / "consensus_summary.json").read_text(encoding="utf-8"))
    assert consensus["peers"]["weighted_pass"] == 3.0
    assert consensus["policy_gate"]["peer_weight_mode"] == "linear"
