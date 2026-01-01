from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

def test_prisma_pipeline_emits_checklist(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "prisma_abstract_pipeline.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "prisma_sample_input.json"

    outdir = tmp_path / "prisma_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert "section_coverage" in metrics
    assert "missing_sections" in metrics
    assert "sections_complete" in flags

    # We intentionally left Limitations blank, so it should be missing:
    assert "Limitations" in metrics["missing_sections"]
    assert flags["sections_complete"] is False

    assert (outdir / "report.json").exists()
    assert (outdir / "checklist.md").exists()
    assert (outdir / "audit_bundle.json").exists()