from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


def test_coherence_audit_sample(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "coherence_audit.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "coherence_audit_sample.json"

    outdir = tmp_path / "coherence_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "coherence_audit.json").exists()
    assert (outdir / "coherence_audit.md").exists()
    assert (outdir / "coherence_claims.csv").exists()

    # the sample should normally pass; if you set very strict thresholds, relax them in the YAML
    assert "overall_pass" in flags
