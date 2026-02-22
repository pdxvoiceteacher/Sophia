#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import zipfile
from pathlib import Path
from typing import Iterable

FORBIDDEN_PATTERNS = [
    re.compile(r"sk-[A-Za-z0-9]{16,}"),
    re.compile(r"(?i)api[_-]?key\s*[:=]\s*[A-Za-z0-9_\-]{8,}"),
    re.compile(r"(?i)bearer\s+[A-Za-z0-9_\-.]{8,}"),
]

ALLOWED_FILES = [
    "epoch.json",
    "epoch_metrics.json",
    "epoch_findings.json",
    "sophia_audit.json",
    "sophia_plan.json",
    "telemetry.json",
    "epistemic_graph.json",
    "tel.json",
    "tel_events.jsonl",
]


def file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def scan_for_secrets(paths: Iterable[Path]) -> list[str]:
    hits: list[str] = []
    for path in paths:
        if not path.exists() or not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        for pattern in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                hits.append(f"{path.name}: {pattern.pattern}")
    return hits


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--submission-id", required=True)
    ap.add_argument("--submitter-id", default="local-operator")
    args = ap.parse_args()

    run_dir = Path(args.run_dir).resolve()
    out_dir = Path(args.out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    included = [run_dir / name for name in ALLOWED_FILES if (run_dir / name).exists()]
    if not included:
        raise SystemExit("No eligible artifacts found in run-dir.")

    hits = scan_for_secrets(included)
    if hits:
        raise SystemExit("Forbidden secret-like patterns detected: " + "; ".join(hits))

    submission = {
        "schema": "cross_review_submission_v1",
        "submission_id": args.submission_id,
        "submitter_id": args.submitter_id,
        "run_dir": str(run_dir),
        "artifacts": [{"name": p.name, "sha256": file_sha(p)} for p in included],
        "redaction_rule": "No secrets: reject token/api-key/bearer-like patterns.",
    }

    submission_path = out_dir / "submission.json"
    submission_path.write_text(json.dumps(submission, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    bundle_path = out_dir / "bundle.zip"
    with zipfile.ZipFile(bundle_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.write(submission_path, arcname="submission.json")
        for p in included:
            zf.write(p, arcname=f"artifacts/{p.name}")

    build_result = {
        "submission_path": str(submission_path),
        "bundle_path": str(bundle_path),
    }
    (out_dir / "build_result.json").write_text(json.dumps(build_result, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
