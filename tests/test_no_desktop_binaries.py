from __future__ import annotations

from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN_EXTENSIONS = {".png", ".ico", ".icns", ".zip", ".exe", ".dll"}


def tracked_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        check=True,
        capture_output=True,
        text=True,
        cwd=ROOT,
    )
    return result.stdout.splitlines()


def test_no_desktop_binary_assets_tracked() -> None:
    offenders = []
    for path in tracked_files():
        if not path.startswith("desktop/"):
            continue
        suffix = Path(path).suffix.lower()
        if suffix in FORBIDDEN_EXTENSIONS:
            offenders.append(path)
    assert not offenders, f"Binary assets are not allowed under desktop/: {', '.join(offenders)}"
