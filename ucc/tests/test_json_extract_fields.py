from pathlib import Path
from ucc.core import run_module

def test_json_extract_fields_step(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "json_extract_fields.yml"
    input_path = repo / "tasks" / "json_extract_fields_sample.json"

    outdir = tmp_path / "json_extract_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema)

    assert flags.get("json_extract_ok") is True
    assert (outdir / "extracted_metrics.json").exists()
    assert (outdir / "extracted_metrics.csv").exists()
    assert (outdir / "extracted_metrics.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()