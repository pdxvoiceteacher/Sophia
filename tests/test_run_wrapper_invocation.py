from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[1]


def test_run_wrapper_help_succeeds_for_module_and_script_invocation() -> None:
    module_cmd = [sys.executable, "-m", "tools.telemetry.run_wrapper", "-h"]
    script_cmd = [sys.executable, str(REPO / "tools" / "telemetry" / "run_wrapper.py"), "-h"]

    module = subprocess.run(module_cmd, cwd=REPO, capture_output=True, text=True)
    script = subprocess.run(script_cmd, cwd=REPO, capture_output=True, text=True)

    assert module.returncode == 0, module.stderr
    assert script.returncode == 0, script.stderr
    assert "--emit-tel-events" in module.stdout
    assert "--simulate-peers" in script.stdout


def test_policy_thresholds_template_validates_against_schema() -> None:
    schema = json.loads((REPO / "schema" / "policy_thresholds_v1.schema.json").read_text(encoding="utf-8-sig"))
    template = json.loads((REPO / "config" / "policy_thresholds.json").read_text(encoding="utf-8-sig"))

    Draft202012Validator(schema).validate(template)
