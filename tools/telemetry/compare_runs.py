#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, Any

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def get_metrics(doc: dict) -> Dict[str, float]:
    # telemetry.json uses {"metrics": {...}}
    if isinstance(doc.get("metrics"), dict):
        m = doc["metrics"]
    else:
        m = doc
    out: Dict[str, float] = {}
    for k, v in (m or {}).items():
        try:
            out[k] = float(v)
        except Exception:
            continue
    return out

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline")
    ap.add_argument("candidate")
    ap.add_argument("--rel", type=float, default=0.02, help="Relative tolerance (default 0.02)")
    ap.add_argument("--abs-floor", type=float, default=0.01, help="Denominator floor for near-zero baselines (default 0.01)")
    ap.add_argument("--keys", default="", help="Comma-separated keys to compare (default: all common metric keys)")
    args = ap.parse_args()

    bdoc = load(Path(args.baseline))
    cdoc = load(Path(args.candidate))
    b = get_metrics(bdoc)
    c = get_metrics(cdoc)

    if args.keys.strip():
        keys = [k.strip() for k in args.keys.split(",") if k.strip()]
    else:
        keys = sorted(set(b.keys()) & set(c.keys()))

    if not keys:
        print("[compare_runs] FAIL no common metric keys found")
        return 2

    failed = False
    for k in keys:
        bv = float(b[k])
        cv = float(c[k])
        diff = abs(cv - bv)
        denom = max(abs(bv), float(args.abs_floor))
        rel = diff / denom

        if rel > float(args.rel):
            print(f"[compare_runs] FAIL {k}: baseline={bv} candidate={cv} (rel={rel:.3f} > {args.rel})")
            failed = True

    if failed:
        return 2

    print("[compare_runs] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
