#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from datetime import datetime, timezone
from pathlib import Path

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True, help="Run directory (e.g., out/telemetry_smoke)")
    ap.add_argument("--telemetry", required=True)
    ap.add_argument("--state", required=True)
    ap.add_argument("--decision", required=True)
    ap.add_argument("--out", required=True, help="proposal.json output path")
    ap.add_argument("--git-commit", default="", help="Optional git commit string")
    args = ap.parse_args()

    run_dir = Path(args.run_dir)
    tel_p = Path(args.telemetry)
    st_p  = Path(args.state)
    dec_p = Path(args.decision)

    tel = load(tel_p)
    st  = load(st_p)
    dec = load(dec_p)

    # Convert recommendations into change proposals (proposal-only; no auto-apply)
    changes = []
    recs = st.get("recommendations", []) or []
    for i, r in enumerate(recs, start=1):
        changes.append({
            "id": f"chg-{i:03d}",
            "action": r.get("action","unknown"),
            "priority": r.get("priority","medium"),
            "why": r.get("why",""),
            "targets": [],
            "diff_hint": "",
            "risk_ids": [],
            "expected_effects": {}
        })

    # If no recommendations (green state), create a low-priority maintenance proposal
    if not changes:
        changes.append({
            "id": "chg-001",
            "action": "noop_maintain_green",
            "priority": "low",
            "why": "System is green; maintain baselines and keep telemetry consistent.",
            "targets": ["tests/baselines/*", ".github/workflows/ci.yml"],
            "diff_hint": "No changes required; only update baselines intentionally when expected.",
            "risk_ids": [],
            "expected_effects": {"goal": "stability"}
        })

    proposal = {
        "schema_id": "coherencelattice.change_proposal.v1",
        "version": 1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "basis": {
            "run_dir": str(run_dir).replace("\\","/"),
            "git_commit": args.git_commit,
            "telemetry_sha256": sha256_file(tel_p),
            "state_sha256": sha256_file(st_p),
            "decision_sha256": sha256_file(dec_p)
        },
        "decision": dec,
        "changes": changes,
        "notes": "Proposal-only. No auto-apply. Requires human/CI review per governance."
    }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(proposal, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[propose_change] wrote {outp}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
