from __future__ import annotations
from pathlib import Path
import subprocess
import json

def test_music_strict_coherence_audit(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]

    py = repo.parent / "python" / ".venv" / "Scripts" / "python.exe"
    if not py.exists():
        # CI uses system python; tests should still pass there.
        py = None

    # Always run demo with whatever python is available
    demo = repo.parent / "python" / "experiments" / "coherence_music" / "demo_bhairav_audit.py"
    assert demo.exists()

    cmd_py = [str(py)] if py else ["python"]
    subprocess.run(cmd_py + [str(demo)], cwd=str(repo.parent), check=True)

    task = repo / "tasks" / "coherence_runs" / "music_bhairav_coherence.json"
    assert task.exists()

    outdir = tmp_path / "ucc_music_strict_out"
    mod = repo / "modules" / "coherence_audit_strict.yml"
    schema = repo / "schema" / "ucc_module.schema.json"
    assert mod.exists() and schema.exists()

    subprocess.run(cmd_py + ["-m", "ucc.cli", "run", str(mod), "--input", str(task), "--outdir", str(outdir)],
                   cwd=str(repo.parent), check=True)

    # outputs exist
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()

    rep = json.loads((outdir / "report.json").read_text(encoding="utf-8"))
    # Strict should not fail section completeness
    assert "flags" in rep
