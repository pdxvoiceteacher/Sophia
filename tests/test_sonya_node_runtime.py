from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator

from python.sonya_node.runtime import SonyaNodeConfig, SonyaNodeRuntime

REPO = Path(__file__).resolve().parents[1]


def test_sonya_node_runtime_writes_valid_telemetry_and_summary(monkeypatch, tmp_path: Path, capsys) -> None:
    runtime = SonyaNodeRuntime(
        repo_root=REPO,
        config=SonyaNodeConfig(
            node_id="test-node",
            compute_class="cpu_only",
            telemetry_endpoint=str(tmp_path / "sonya-node-records"),
            enabled_task_types={"sophia_echo": True},
        ),
    )

    def _fake_runner(prompt: str, out_dir: Path) -> Path:
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "evidence_bundle.json").write_text('{"ok": true}\n', encoding="utf-8")
        telemetry_payload = {
            "metrics": {
                "E": 0.5,
                "T": 0.9,
                "Psi": 0.7,
                "DeltaS": 0.1,
                "Lambda": 0.4,
                "Es": 0.3,
            }
        }
        telemetry_path = out_dir / "telemetry.json"
        telemetry_path.write_text(json.dumps(telemetry_payload) + "\n", encoding="utf-8")
        return telemetry_path

    monkeypatch.setattr(runtime, "_invoke_telemetry_wrapper", _fake_runner)

    result = runtime.run_local_task("test prompt")

    assert result["path"].exists()
    record = json.loads(result["path"].read_text(encoding="utf-8"))
    schema = json.loads((REPO / "schema" / "sonya_node_telemetry.schema.json").read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(record)
    assert record["node_id"] == "test-node"
    assert record["status"] == "success"
    captured = capsys.readouterr()
    assert "Sonya Node test-node ran task" in captured.out


def test_sonya_node_cli_help_supports_module_and_script_invocation() -> None:
    script = subprocess.run(
        [sys.executable, "tools/sonya_node/run_sonya_node.py", "-h"],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    module = subprocess.run(
        [sys.executable, "-m", "tools.sonya_node.run_sonya_node", "-h"],
        cwd=REPO,
        capture_output=True,
        text=True,
    )

    assert script.returncode == 0, script.stderr
    assert module.returncode == 0, module.stderr
    assert "usage" in f"{script.stdout}\n{script.stderr}".lower()
    assert "usage" in f"{module.stdout}\n{module.stderr}".lower()
