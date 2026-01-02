from __future__ import annotations

from pathlib import Path
import shutil

from ucc.core import run_module


def test_check_lean_symbols_step(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "quantum_anchor_lean_symbols.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "quantum_anchor_lean_symbols_sample.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "ScratchLeanSymbols.lean").exists()
    assert (outdir / "lean_check.log").exists()

    lake = shutil.which("lake") or shutil.which("lake.exe")
    if lake is None:
        assert flags.get("lean_symbols_skipped") is True
    else:
        # If lake exists, it should actually run (pass or fail depending on repo state);
        # for your repo (green build), it should pass.
        assert flags.get("lean_symbols_skipped") is False
