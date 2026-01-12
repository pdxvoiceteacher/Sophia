#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Optional


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def resolve_artifact(raw: str, run_dir: Path, repo_root: Path) -> Optional[Path]:
    """
    Resolve artifacts robustly across environments.

    Supported forms:
      1) absolute paths
      2) repo-root relative paths (e.g., out/.../run_x/file.json)
      3) run-dir relative paths (e.g., konomi_smoke_base/file.json)
      4) repo-root relative paths that include the run_dir prefix; we strip it and retry
    """
    raw_norm = raw.replace("/", "\\")
    p = Path(raw_norm)

    # Absolute
    if p.is_absolute() and p.exists():
        return p

    # 2) Repo-root relative
    cand_repo = repo_root / p
    if cand_repo.exists():
        return cand_repo

    # 3) Run-dir relative
    cand_run = run_dir / p
    if cand_run.exists():
        return cand_run

    # 4) If raw includes the run_dir prefix, strip it and try again
    try:
        run_rel = run_dir.relative_to(repo_root).as_posix().replace("/", "\\")
        if raw_norm.startswith(run_rel + "\\"):
            tail = raw_norm[len(run_rel) + 1 :]
            cand_strip = run_dir / tail
            if cand_strip.exists():
                return cand_strip
    except Exception:
        pass

    return None


def infer_repo_root(start: Path) -> Path:
    cur = start.resolve()
    while cur != cur.parent:
        if (cur / ".git").exists():
            return cur
        cur = cur.parent
    return start.resolve()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("telemetry_json", help="Path to telemetry.json")
    ap.add_argument("--repo-root", default="", help="Repo root (default: inferred by walking up to .git)")
    args = ap.parse_args()

    tele = Path(args.telemetry_json).resolve()
    run_dir = tele.parent

    if args.repo_root:
        repo_root = Path(args.repo_root).resolve()
    else:
        repo_root = infer_repo_root(run_dir)

    doc = json.loads(tele.read_text(encoding="utf-8"))

    if not doc.get("flags", {}).get("telemetry_ok", False):
        print("[verify_artifacts] FAIL telemetry_ok is false")
        return 2

    artifacts = doc.get("artifacts") or []
    if not artifacts:
        print("[verify_artifacts] FAIL no artifacts listed")
        return 2

    failed = False
    for a in artifacts:
        raw = str(a.get("path", ""))
        expected = str(a.get("sha256", "")).lower()

        resolved = resolve_artifact(raw, run_dir, repo_root)
        if not resolved:
            print(f"[verify_artifacts] FAIL missing artifact: raw={raw}")
            failed = True
            continue

        actual = sha256_file(resolved).lower()
        if actual != expected:
            print(f"[verify_artifacts] FAIL sha256 mismatch: raw={raw}")
            print(f"  expected={expected}")
            print(f"    actual={actual}")
            failed = True

    if failed:
        return 2

    print("[verify_artifacts] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

