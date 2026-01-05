from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


def test_ucc_governance_guardrail(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "ucc_governance_guardrail.yml"
    input_path = repo / "tasks" / "ucc_governance_guardrail_sample.json"

    outdir = tmp_path / "ucc_guardrail_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema)

    assert flags.get("sections_complete") is True
    assert flags.get("authority_profile_ok") is True
    assert flags.get("authority_deep_validation_ok") is True

    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "ucc_governance_guardrail_checklist.md").exists()