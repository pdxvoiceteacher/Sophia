from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def _has_usage(result: subprocess.CompletedProcess[str]) -> bool:
    combined = f"{result.stdout}\n{result.stderr}".lower()
    return "usage" in combined


def test_run_wrapper_help_succeeds_via_script_path_and_module() -> None:
    script = subprocess.run(
        [sys.executable, "tools/telemetry/run_wrapper.py", "-h"],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    module = subprocess.run(
        [sys.executable, "-m", "tools.telemetry.run_wrapper", "-h"],
        cwd=REPO,
        capture_output=True,
        text=True,
    )

    assert script.returncode == 0, script.stderr
    assert module.returncode == 0, module.stderr
    assert _has_usage(script)
    assert _has_usage(module)
