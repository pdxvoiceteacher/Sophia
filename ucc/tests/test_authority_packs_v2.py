from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


CASES = [
    ("modules/authority_nist_csf_profile_coverage.yml", "tasks/authority_packs/nist_csf_profile_task.json"),
    ("modules/authority_iso27001_profile_coverage.yml", "tasks/authority_packs/iso27001_profile_task.json"),
    ("modules/authority_iso42001_profile_coverage.yml", "tasks/authority_packs/iso42001_profile_task.json"),
]


def test_authority_packs_v2(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"

    for mod_rel, task_rel in CASES:
        module_path = repo / mod_rel
        input_path = repo / task_rel
        outdir = tmp_path / module_path.stem

        metrics, flags = run_module(module_path, input_path, outdir, schema)

        # expect validation flags present
        assert "authority_profile_ok" in flags
        assert flags["authority_profile_ok"] is True

        # expect outputs
        assert (outdir / "report.json").exists()
        assert (outdir / "audit_bundle.json").exists()
        assert (outdir / "authority_profile_checklist.md").exists()