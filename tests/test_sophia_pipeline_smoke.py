from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator


def test_sophia_pipeline_smoke(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    telemetry = {
        "run_id": "smoke-run",
        "claims": [],
        "metrics": {},
        "artifacts": [],
        "schema_id": "telemetry_v1",
    }
    graph = {"nodes": [], "edges": []}

    (run_dir / "telemetry.json").write_text(
        json.dumps(telemetry, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    (run_dir / "epistemic_graph.json").write_text(
        json.dumps(graph, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    result = subprocess.run(
        [
            sys.executable,
            "tools/telemetry/sophia_audit.py",
            "--run-dir",
            str(run_dir),
            "--repo-root",
            ".",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0

    audit_path = run_dir / "sophia_audit.json"
    plan_path = run_dir / "sophia_plan.json"
    assert audit_path.exists()
    assert plan_path.exists()

    audit = json.loads(audit_path.read_text(encoding="utf-8-sig"))
    plan = json.loads(plan_path.read_text(encoding="utf-8-sig"))

    audit_schema = json.loads(Path("schema/sophia_audit.schema.json").read_text(encoding="utf-8-sig"))
    plan_schema = json.loads(Path("schema/sophia_plan_v1.schema.json").read_text(encoding="utf-8-sig"))

    Draft202012Validator(audit_schema).validate(audit)
    Draft202012Validator(plan_schema).validate(plan)
