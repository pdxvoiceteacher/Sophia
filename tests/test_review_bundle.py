from __future__ import annotations

import json
import subprocess
import sys
import zipfile
from pathlib import Path


def write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_review_bundle_rejects_secret_patterns(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    out_dir = tmp_path / "out"
    run_dir.mkdir()
    write_json(run_dir / "epoch.json", {"ok": True})
    (run_dir / "tel.json").write_text('{"token":"sk-1234567890ABCDEFG"}\n', encoding="utf-8")

    cmd = [
        sys.executable,
        "tools/telemetry/build_review_bundle.py",
        "--run-dir",
        str(run_dir),
        "--out-dir",
        str(out_dir),
        "--submission-id",
        "sub-test",
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    assert result.returncode != 0
    assert "Forbidden secret-like patterns" in (result.stdout + result.stderr)


def test_review_bundle_outputs_submission_and_zip(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    out_dir = tmp_path / "out"
    run_dir.mkdir()
    write_json(run_dir / "epoch.json", {"epoch_id": "e1"})
    write_json(run_dir / "epoch_metrics.json", {"epoch_id": "e1", "step_series": [], "thresholds": {}})
    write_json(run_dir / "epoch_findings.json", {"epoch_id": "e1", "findings": []})
    write_json(run_dir / "tel.json", {"graph": {"nodes": [], "edges": []}})

    subprocess.run(
        [
            sys.executable,
            "tools/telemetry/build_review_bundle.py",
            "--run-dir",
            str(run_dir),
            "--out-dir",
            str(out_dir),
            "--submission-id",
            "sub-clean",
            "--submitter-id",
            "anon-1",
        ],
        check=True,
    )

    submission = json.loads((out_dir / "submission.json").read_text(encoding="utf-8"))
    assert submission["submission_id"] == "sub-clean"
    assert submission["submitter_id"] == "anon-1"

    with zipfile.ZipFile(out_dir / "bundle.zip") as zf:
        names = set(zf.namelist())
    assert "submission.json" in names
    assert "artifacts/epoch.json" in names
