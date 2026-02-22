from __future__ import annotations

from pathlib import Path
import shutil


ROOT = Path(__file__).resolve().parents[1]
HOOKS_DIR = ROOT / ".githooks"
GIT_HOOKS_DIR = ROOT / ".git" / "hooks"


def main() -> int:
    if not HOOKS_DIR.exists():
        print("Missing .githooks directory.")
        return 1
    GIT_HOOKS_DIR.mkdir(parents=True, exist_ok=True)
    for hook in HOOKS_DIR.iterdir():
        if not hook.is_file():
            continue
        target = GIT_HOOKS_DIR / hook.name
        shutil.copy2(hook, target)
        target.chmod(0o755)
        print(f"Installed {hook.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
