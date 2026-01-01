from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

def test_nist_ai_600_1_genai_profile_pipeline(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "nist_ai_600_1_genai_profile.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "nist_ai_600_1_genai_sample.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert flags["sections_complete"] is True
    assert metrics["required_count"] == 5
    assert metrics["present_count"] == 5

    assert (outdir / "genai_profile_checklist.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
