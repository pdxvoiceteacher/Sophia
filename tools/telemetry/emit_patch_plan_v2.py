from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List


def _now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _canonical(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


ALLOW_PREFIXES = ["config/plasticity/", "governance/", "schema/"]
DENY_PREFIXES = [".github/", "tools/", "ucc/", "python/", "config/"]
BUDGET_KEYS = [
    "perturb", "retry", "timeout", "concurrency", "parallel", "workers", "matrix",
    "interval", "freq", "schedule", "max_", "attempt", "budget"
]


def _ops_from_action_v2(proposal: Dict[str, Any]) -> List[Dict[str, Any]]:
    ops: List[Dict[str, Any]] = []
    recs = proposal.get("recommendations") or []
    if not isinstance(recs, list):
        return ops

    for rec in recs:
        if not isinstance(rec, dict):
            continue
        act = rec.get("action_v2")
        if not isinstance(act, dict):
            continue
        op = act.get("op")
        path = act.get("path")
        if op not in ("json_set", "text_replace") or not isinstance(path, str):
            continue

        if op == "json_set":
            ops.append({
                "op": "json_set",
                "path": path,
                "json_path": act.get("json_path"),
                "value": act.get("value"),
                "note": rec.get("id") or rec.get("suggestion"),
            })
        elif op == "text_replace":
            ops.append({
                "op": "text_replace",
                "path": path,
                "pattern": act.get("pattern"),
                "replacement": act.get("replacement"),
                "max_replacements": act.get("max_replacements"),
                "note": rec.get("id") or rec.get("suggestion"),
            })

    return ops


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", required=True)
    ap.add_argument("--out", required=True, help="Patch plan output path")
    ap.add_argument("--created-at-utc", default="")
    args = ap.parse_args()

    proposal = json.loads(Path(args.proposal).read_text(encoding="utf-8"))
    pid = proposal.get("proposal_id") or hashlib.sha256(_canonical(proposal).encode("utf-8")).hexdigest()[:12]
    created_at = args.created_at_utc.strip() or _now_utc_iso()

    ops = _ops_from_action_v2(proposal)

    plan = {
        "schema": "plasticity_patch_plan_v2",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "guardrails": {
            "allow_prefixes": ALLOW_PREFIXES,
            "deny_prefixes": DENY_PREFIXES,
            "budget_keys": BUDGET_KEYS
        },
        "operations": ops
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(plan, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(str(out_path).replace("\\", "/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
