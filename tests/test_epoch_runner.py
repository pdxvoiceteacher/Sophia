from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator


def hash_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path, schema_path: Path) -> None:
    payload = json.loads(path.read_text(encoding="utf-8-sig"))
    schema = json.loads(schema_path.read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(payload)


def test_epoch_runner_deterministic_replay_and_schemas(tmp_path: Path) -> None:
    run_a = tmp_path / "run_a"
    run_b = tmp_path / "run_b"

    cmd_base = [
        sys.executable,
        "tools/telemetry/run_epoch.py",
        "--prompt-text",
        "Behavioral-only epoch prompt.",
        "--mode",
        "deterministic",
        "--seed",
        "42",
        "--emit-tel",
        "--emit-tel-events",
    ]
    subprocess.run([*cmd_base, "--out", str(run_a)], check=True)
    subprocess.run([*cmd_base, "--out", str(run_b)], check=True)

    assert hash_file(run_a / "epoch.json") == hash_file(run_b / "epoch.json")

    validate(run_a / "epoch.json", Path("schema/agency_epoch_v1.schema.json"))
    validate(run_a / "epoch_metrics.json", Path("schema/agency_epoch_metrics_v1.schema.json"))
    validate(run_a / "epoch_findings.json", Path("schema/agency_epoch_findings_v1.schema.json"))
