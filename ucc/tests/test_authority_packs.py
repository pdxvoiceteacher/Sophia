from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


def _run(tmp_path: Path, module_rel: str, task_rel: str) -> None:
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / module_rel
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / task_rel
    outdir = tmp_path / module_path.stem
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)
    assert flags["sections_complete"] is True
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()


def test_nist_csf_pack(tmp_path: Path):
    _run(tmp_path, "modules/authority_packs/nist_csf_profile_coverage.yml",
         "tasks/authority_packs/nist_csf_profile_sample.json")


def test_iso27001_pack(tmp_path: Path):
    _run(tmp_path, "modules/authority_packs/iso27001_isms_profile_coverage.yml",
         "tasks/authority_packs/iso27001_isms_profile_sample.json")


def test_iso42001_pack(tmp_path: Path):
    _run(tmp_path, "modules/authority_packs/iso42001_aims_profile_coverage.yml",
         "tasks/authority_packs/iso42001_aims_profile_sample.json")