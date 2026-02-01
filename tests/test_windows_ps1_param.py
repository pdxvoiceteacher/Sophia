from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WINDOWS_SCRIPTS = ROOT / "scripts" / "windows"


def first_nonempty_noncomment_line(text: str) -> str | None:
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            continue
        return stripped
    return None


def test_windows_ps1_param_first_statement() -> None:
    assert WINDOWS_SCRIPTS.exists(), "scripts/windows directory missing"
    failures = []
    for script_path in sorted(WINDOWS_SCRIPTS.glob("*.ps1")):
        content = script_path.read_text(encoding="utf-8-sig")
        first_line = first_nonempty_noncomment_line(content)
        if not first_line or not first_line.lower().startswith("param"):
            failures.append(script_path.name)
    assert not failures, f"param(...) must be first statement in: {', '.join(failures)}"
