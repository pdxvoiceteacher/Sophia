from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.telemetry import run_wrapper


def test_write_evidence_and_consensus_uses_outdir_relative_artifacts(tmp_path: Path) -> None:
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
