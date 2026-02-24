from __future__ import annotations

from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN_EXTENSIONS = {".ico", ".icns", ".exe", ".dll"}
ALLOWLIST_PREFIXES = {"release_artifacts/"}


def tracked_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        check=True,
        capture_output=True,
        text=True,
        cwd=ROOT,
    )
    return result.stdout.splitlines()


def is_allowlisted(path: str) -> bool:
    return any(path.startswith(prefix) for prefix in ALLOWLIST_PREFIXES)


def main() -> int:
    offenders = []
    for path in tracked_files():
        suffix = Path(path).suffix.lower()
        if suffix in FORBIDDEN_EXTENSIONS and not is_allowlisted(path):
            offenders.append(path)
    if offenders:
        print("Binary assets are not allowed in this repo:")
        for path in offenders:
            print(f"- {path}")
        return 1
    print("No forbidden binary assets found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
