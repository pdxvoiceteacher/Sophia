from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WINDOWS_SCRIPTS = ROOT / "scripts" / "windows"


def first_nonempty_noncomment_line(text: str) -> tuple[int, str] | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            continue
        return idx, line
    return None


def test_windows_ps1_param_first_statement() -> None:
    assert WINDOWS_SCRIPTS.exists(), "scripts/windows directory missing"
    failures = []
    for script_path in sorted(WINDOWS_SCRIPTS.glob("*.ps1")):
        data = script_path.read_bytes()
        if data.startswith(b"\xef\xbb\xbf"):
            failures.append(f"{script_path.name} (utf-8 BOM detected)")
            continue
        content = data.decode("utf-8")
        first_line_info = first_nonempty_noncomment_line(content)
        if not first_line_info:
            failures.append(f"{script_path.name} (missing param)")
            continue
        line_number, line = first_line_info
        if line_number != 1:
            failures.append(f"{script_path.name} (param must be line 1)")
            continue
        if line != line.lstrip():
            failures.append(f"{script_path.name} (leading whitespace before param)")
            continue
        if not line.lower().startswith("param"):
            failures.append(f"{script_path.name} (param must be first statement)")
    assert not failures, f"param(...) must be first statement in: {', '.join(failures)}"
