#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, shutil
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
PROPOSALS = REPO / "governance" / "proposals"
QUEUE = PROPOSALS / "queue"
APPROVED = PROPOSALS / "approved"
REJECTED = PROPOSALS / "rejected"

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()

def now_z() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%SZ")

def short_id(sha: str) -> str:
    return sha[:12]

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["ingest"])
    ap.add_argument("--proposal", required=True)
    ap.add_argument("--status", default="queue", choices=["queue","approved","rejected"])
    ap.add_argument("--note", default="")
    args = ap.parse_args()

    PROPOSALS.mkdir(parents=True, exist_ok=True)
    QUEUE.mkdir(parents=True, exist_ok=True)
    APPROVED.mkdir(parents=True, exist_ok=True)
    REJECTED.mkdir(parents=True, exist_ok=True)

    src = Path(args.proposal)
    if not src.exists():
        raise SystemExit(f"Missing proposal: {src}")

    sha = sha256_file(src)
    pid = short_id(sha)

    doc = load(src)
    decision = ""
    try:
        decision = str(((doc.get("decision") or {}).get("decision")) or "")
    except Exception:
        decision = ""

    name = f"{now_z()}__{pid}__{decision or 'unknown'}.json"

    dst_dir = {"queue":QUEUE,"approved":APPROVED,"rejected":REJECTED}[args.status]
    dst = dst_dir / name
    shutil.copy2(src, dst)

    print(f"[proposal_queue] ingested -> {dst}")
    if args.note:
        print("[proposal_queue] note:", args.note)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
