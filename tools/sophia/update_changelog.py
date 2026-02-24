#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from jsonschema import Draft202012Validator


REPO_ROOT = Path(__file__).resolve().parents[2]
CHANGELOG_PATH = REPO_ROOT / "docs" / "standards_changelog.json"
SCHEMA_PATH = REPO_ROOT / "schema" / "standards_changelog.schema.json"


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def save_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def git_commit() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        return result.stdout.strip()
    except Exception:
        return "unknown"


def validate(payload: dict) -> None:
    schema = load_json(SCHEMA_PATH)
    validator = Draft202012Validator(schema)
    errors = sorted(validator.iter_errors(payload), key=lambda e: e.path)
    if errors:
        message = "; ".join(f"{list(err.path)} {err.message}" for err in errors[:10])
        raise ValueError(f"Changelog validation failed: {message}")


def main() -> int:
    ap = argparse.ArgumentParser(description="Append to standards changelog.")
    ap.add_argument("--version", required=True, help="Semver-like version string")
    ap.add_argument("--summary", required=True, help="Summary of changes")
    ap.add_argument("--date", default="", help="Override date (YYYY-MM-DD)")
    ap.add_argument("--commit", default="", help="Override commit hash")
    args = ap.parse_args()

    changelog = load_json(CHANGELOG_PATH) if CHANGELOG_PATH.exists() else {"entries": []}
    date_value = args.date or datetime.now(timezone.utc).date().isoformat()
    commit_value = args.commit or git_commit()

    entry = {
        "version": args.version,
        "date": date_value,
        "summary": args.summary,
        "commit": commit_value,
    }
    changelog.setdefault("entries", []).append(entry)
    validate(changelog)
    save_json(CHANGELOG_PATH, changelog)
    print("[update_changelog] OK", entry)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
