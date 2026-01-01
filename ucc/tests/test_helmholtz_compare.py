from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

def test_helmholtz_compare_sample(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "helmholtz_compare.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "helmholtz_compare_sample.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert "deltaPsi_peak" in metrics
    assert "auc_deltaPsi" in metrics
    assert flags["overall_pass"] is True

    assert (outdir / "comparison.md").exists()
    assert (outdir / "comparison.json").exists()
    assert (outdir / "delta_curve.csv").exists()
    assert (outdir / "delta_curve.md").exists()
    assert (outdir / "audit_bundle.json").exists()