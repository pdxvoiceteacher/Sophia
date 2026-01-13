#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Dict


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission-dir", required=True, help="Folder containing submission.json")
    ap.add_argument("--out", default="", help="Output path (default: <submission-dir>/submission_receipt.json)")
    args = ap.parse_args()

    subdir = Path(args.submission_dir).resolve()
    sub_json = subdir / "submission.json"
    if not sub_json.exists():
        raise SystemExit(f"[make_submission_receipt] FAIL missing {sub_json}")

    # Hash all files under submission dir except previous receipts/reports
    files = []
    for p in sorted(subdir.rglob("*")):
        if p.is_dir():
            continue
        rel = p.relative_to(subdir).as_posix()
        if rel in ("submission_receipt.json", "ingest_report.json"):
            continue
        files.append(p)

    manifest: List[Dict[str, str]] = []
    for p in files:
        manifest.append({"path": p.relative_to(subdir).as_posix(), "sha256": sha256_file(p)})

    # Canonical manifest hash
    canonical = json.dumps(manifest, sort_keys=True, ensure_ascii=False).encode("utf-8")
    submission_sha = hashlib.sha256(canonical).hexdigest()

    receipt = {
        "schema": "submission_receipt_v1",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "submission_sha256": submission_sha,
        "file_count": len(manifest),
        "manifest": manifest,
    }

    outp = Path(args.out) if args.out else (subdir / "submission_receipt.json")
    outp.write_text(json.dumps(receipt, sort_keys=True, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"[make_submission_receipt] OK wrote {outp} sha={submission_sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
