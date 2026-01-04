from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

CASES = [
    ("modules/authority_cis_benchmarks_profile_coverage.yml", "tasks/authority_packs/cis_benchmarks_profile_task.json"),
    ("modules/authority_owasp_top10_profile_coverage.yml", "tasks/authority_packs/owasp_top10_profile_task.json"),
    ("modules/authority_owasp_samm_profile_coverage.yml", "tasks/authority_packs/owasp_samm_profile_task.json"),
]

def test_authority_packs_cisbench_top10_samm(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    for mod_rel, task_rel in CASES:
        module_path = repo / mod_rel
        input_path = repo / task_rel
        outdir = tmp_path / module_path.stem
        metrics, flags = run_module(module_path, input_path, outdir, schema)
        assert flags.get("authority_deep_validation_ok") is True
        assert (outdir / "report.json").exists()
        assert (outdir / "audit_bundle.json").exists()
        assert (outdir / "authority_profile_checklist.md").exists()