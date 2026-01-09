#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--decision", required=True, help="control_decision.json")
    ap.add_argument("--allow-slow", action="store_true", help="Allow decision=slow in CI")
    ap.add_argument("--allow-reroute", action="store_true", help="Allow decision=reroute in CI")
    args = ap.parse_args()

    d = load(Path(args.decision))
    decision = d.get("decision","")

    hard_fail = {"halt","escalate"}
    if decision in hard_fail:
        print(f"[enforce_policy_gate] FAIL decision={decision}")
        return 2

    if decision == "slow" and not args.allow_slow:
        print("[enforce_policy_gate] FAIL decision=slow (not allowed)")
        return 2

    if decision == "reroute" and not args.allow_reroute:
        print("[enforce_policy_gate] FAIL decision=reroute (not allowed)")
        return 2

    gates = d.get("gates", {}) or {}
    if bool(gates.get("consent_required", False)) or bool(gates.get("human_review_required", False)):
        print("[enforce_policy_gate] FAIL consent/human_review required")
        return 2

    print(f"[enforce_policy_gate] OK decision={decision}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
