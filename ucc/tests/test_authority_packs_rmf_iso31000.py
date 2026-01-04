from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


CASES = [
    ("modules/authority_nist_ai_rmf_profile_coverage.yml", "tasks/authority_packs/nist_ai_rmf_profile_task.json"),
    ("modules/authority_iso31000_profile_coverage.yml", "tasks/authority_packs/iso31000_profile_task.json"),
]


def test_authority_packs_rmf_iso31000(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema_path = repo / "schema" / "ucc_module.schema.json"

    for mod_rel, task_rel in CASES:
        module_path = repo / mod_rel
        input_path = repo / task_rel
        outdir = tmp_path / (module_path.stem + "_out")

        metrics, flags = run_module(module_path, input_path, outdir, schema_path)

        assert flags.get("authority_deep_validation_ok") is True
        assert (outdir / "report.json").exists()
        assert (outdir / "audit_bundle.json").exists()
        assert (outdir / "authority_profile_checklist.md").exists()