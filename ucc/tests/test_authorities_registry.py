from __future__ import annotations

import json
from pathlib import Path
from ucc.core import run_module


def test_authorities_registry_coverage(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "authorities_registry_coverage.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "authorities_registry_task.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert flags["sections_complete"] is True
    assert (outdir / "authorities_registry_checklist.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()


def test_authorities_registry_paths_exist():
    repo_root = Path(__file__).resolve().parents[2]
    idx_path = repo_root / "ucc" / "authorities" / "index.json"
    data = json.loads(idx_path.read_text(encoding="utf-8-sig"))

    assert "authorities" in data and isinstance(data["authorities"], list) and len(data["authorities"]) > 0

    for a in data["authorities"]:
        for key in ["id", "name", "version", "module", "sample_task"]:
            assert key in a, f"Missing key {key} in authority entry: {a}"

        # Paths are stored like "ucc/modules/..." — make them repo-root relative
        mod_path = repo_root / Path(a["module"])
        task_path = repo_root / Path(a["sample_task"])

        assert mod_path.exists(), f"Missing module file: {mod_path}"
        assert task_path.exists(), f"Missing sample task file: {task_path}"