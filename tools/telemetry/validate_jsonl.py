#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl_path", help="Path to JSONL file")
    ap.add_argument("--require-keys", default="", help="Comma-separated keys required in each JSON object")
    args = ap.parse_args()

    p = Path(args.jsonl_path)
    if not p.exists():
        print(f"[validate_jsonl] FAIL missing file: {p}")
        return 2

    required = [k.strip() for k in args.require_keys.split(",") if k.strip()]
    bad = 0
    total = 0

    with p.open("r", encoding="utf-8") as f:
        for ln, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            total += 1
            try:
                obj = json.loads(line)
            except Exception as e:
                print(f"[validate_jsonl] FAIL {p} line {ln}: invalid JSON: {e}")
                bad += 1
                continue
            if required:
                for k in required:
                    if k not in obj:
                        print(f"[validate_jsonl] FAIL {p} line {ln}: missing key '{k}'")
                        bad += 1
                        break

    if bad:
        return 2

    print(f"[validate_jsonl] OK {p} objects={total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
