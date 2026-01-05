from pathlib import Path
from ucc.core import run_module

def test_coherence_music_audit_coverage(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "coherence_music_audit_coverage.yml"
    input_path = repo / "tasks" / "coherence_music_audit_sample.json"
    outdir = tmp_path / "music_cov"

    metrics, flags = run_module(module_path, input_path, outdir, schema)
    assert flags.get("sections_complete") is True
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()