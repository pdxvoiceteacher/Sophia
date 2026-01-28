#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from datetime import datetime, timezone
from pathlib import Path


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def normalize_ratio(value: float | int | None, fallback: float) -> float:
    if value is None:
        return fallback
    ratio = float(value)
    if ratio > 1.0 and ratio <= 100.0:
        ratio = ratio / 100.0
    return max(0.0, min(1.0, ratio))


def in_scope(entry: dict, scope: str) -> bool:
    if not scope:
        return True
    candidate = entry.get("stakeholder_scope") or entry.get("scope") or entry.get("scopes")
    if candidate is None:
        return True
    if isinstance(candidate, str):
        return candidate == scope
    if isinstance(candidate, list):
        return scope in candidate
    return True


def resolve_policy(policy: dict, scope: str) -> dict:
    scopes = policy.get("scopes", {})
    if isinstance(scopes, dict) and scope in scopes:
        return scopes[scope] or {}
    return policy.get("default") or policy.get("policy") or {}


def main() -> int:
    ap = argparse.ArgumentParser(description="Resolve MVSS policy into election thresholds.")
    ap.add_argument("--registry", required=True, help="Path to registry snapshot JSON")
    ap.add_argument("--policy", required=True, help="Path to MVSS policy JSON")
    ap.add_argument("--stakeholder-scope", default="global", help="Scope name for this election")
    ap.add_argument("--out", required=True, help="Path to write resolution artifact JSON")
    args = ap.parse_args()

    registry = load_json(Path(args.registry))
    policy = load_json(Path(args.policy))
    scope = args.stakeholder_scope

    stakeholders = registry.get("stakeholders", [])
    eligible = [entry for entry in stakeholders if in_scope(entry, scope)]
    total_weight = sum(float(entry.get("weight", 1)) for entry in eligible)
    total_count = len(eligible)

    policy_cfg = resolve_policy(policy, scope)
    quorum_ratio = normalize_ratio(policy_cfg.get("quorum_ratio"), fallback=0.6)
    pass_ratio = normalize_ratio(policy_cfg.get("pass_ratio"), fallback=0.5)

    quorum_weight = math.ceil(total_weight * quorum_ratio) if total_weight else 0
    pass_weight = math.ceil(total_weight * pass_ratio) if total_weight else 0

    output = {
        "schema": "mvss_policy_resolution_v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "stakeholder_scope": scope,
        "mvss_policy_ref": policy.get("policy_id") or policy.get("mvss_policy_ref") or "unknown",
        "registry_snapshot_ref": registry.get("snapshot_id")
        or registry.get("registry_snapshot_ref")
        or "unknown",
        "registry_federation": registry.get("registry_federation")
        or {"enabled": False, "peers": []},
        "eligible_stakeholders": {"count": total_count, "weight": total_weight},
        "thresholds": {
            "quorum_ratio": quorum_ratio,
            "pass_ratio": pass_ratio,
            "quorum_weight": quorum_weight,
            "pass_weight": pass_weight,
        },
    }

    Path(args.out).write_text(json.dumps(output, indent=2), encoding="utf-8")
    print(
        "[resolve_mvss_policy] OK",
        f"eligible={total_count}",
        f"weight={total_weight}",
        f"quorum_weight={quorum_weight}",
        f"pass_weight={pass_weight}",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
