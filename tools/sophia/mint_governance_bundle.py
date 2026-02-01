#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

from jsonschema import Draft202012Validator


REPO_ROOT = Path(__file__).resolve().parents[2]
SCHEMA_DIR = REPO_ROOT / "schema" / "governance"


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def validate(schema_path: Path, payload: dict) -> None:
    schema = load_json(schema_path)
    validator = Draft202012Validator(schema)
    errors = sorted(validator.iter_errors(payload), key=lambda e: e.path)
    if errors:
        message = "; ".join(f"{list(err.path)} {err.message}" for err in errors[:10])
        raise ValueError(f"Schema validation failed for {schema_path.name}: {message}")


def normalize_ratio(value: float | int | None, fallback: float) -> float:
    if value is None:
        return fallback
    ratio = float(value)
    if ratio > 1.0 and ratio <= 100.0:
        ratio = ratio / 100.0
    return max(0.0, min(1.0, ratio))


def in_scope(entry: dict, scope: str) -> bool:
    candidate = entry.get("stakeholder_scope")
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
    return policy.get("default") or {}


def make_hash(payload: dict) -> str:
    encoded = json.dumps(payload, sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def parse_translations(items: list[str]) -> dict:
    translations: dict[str, str] = {}
    for item in items:
        if "=" not in item:
            raise ValueError(f"Translation must be in key=value form: {item}")
        key, value = item.split("=", 1)
        translations[key.strip()] = value.strip()
    return translations


def main() -> int:
    ap = argparse.ArgumentParser(description="Mint governance bundle artifacts for a run.")
    ap.add_argument("--registry", required=True, help="Registry snapshot JSON path")
    ap.add_argument("--policy", required=True, help="MVSS policy JSON path")
    ap.add_argument("--stakeholder-scope", default="global", help="Scope for this election")
    ap.add_argument("--ballot-text-primary", required=True, help="Primary ballot prompt text")
    ap.add_argument(
        "--ballot-text-translation",
        action="append",
        default=[],
        help="Translation entries like es=... (repeatable)",
    )
    ap.add_argument(
        "--choices",
        nargs="+",
        default=["yes", "no"],
        help="Choices list for the election (space separated)",
    )
    ap.add_argument("--out-dir", required=True, help="Run directory to write artifacts")
    args = ap.parse_args()

    registry = load_json(Path(args.registry))
    policy = load_json(Path(args.policy))
    scope = args.stakeholder_scope
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    policy_cfg = resolve_policy(policy, scope)
    quorum_ratio = normalize_ratio(policy_cfg.get("quorum_ratio"), fallback=0.6)
    pass_ratio = normalize_ratio(policy_cfg.get("pass_ratio"), fallback=0.5)

    stakeholders = [s for s in registry.get("stakeholders", []) if in_scope(s, scope)]
    total_weight = sum(float(s.get("weight", 1)) for s in stakeholders)
    quorum_threshold = total_weight * quorum_ratio
    pass_threshold = total_weight * pass_ratio

    translations = parse_translations(args.ballot_text_translation)
    ballot_text = {"primary": args.ballot_text_primary, "translations": translations}

    ballots = []
    for idx, stakeholder in enumerate(stakeholders, start=1):
        choice = args.choices[idx % len(args.choices)]
        ballots.append(
            {
                "ballot_id": f"ballot_{idx}",
                "voter_id": stakeholder.get("stakeholder_id", f"stakeholder_{idx}"),
                "ballot_text": ballot_text,
                "choice": choice,
            }
        )

    election_id = f"election_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%SZ')}"
    election = {
        "schema": "election_v1",
        "election_id": election_id,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "stakeholder_scope": scope,
        "mvss_policy_ref": policy.get("policy_id", "unknown"),
        "registry_snapshot_ref": registry.get("snapshot_id", "unknown"),
        "registry_federation": registry.get("registry_federation", {"enabled": False, "peers": []}),
        "ballots": ballots,
    }

    totals: dict[str, dict[str, float]] = {}
    for ballot in ballots:
        choice = ballot["choice"]
        weight = float(
            next(
                (
                    s.get("weight", 1)
                    for s in stakeholders
                    if s.get("stakeholder_id") == ballot["voter_id"]
                ),
                1,
            )
        )
        totals.setdefault(choice, {"count": 0, "weight": 0})
        totals[choice]["count"] += 1
        totals[choice]["weight"] += weight

    resolution = {
        "schema": "mvss_policy_resolution_v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "stakeholder_scope": scope,
        "mvss_policy_ref": policy.get("policy_id", "unknown"),
        "registry_snapshot_ref": registry.get("snapshot_id", "unknown"),
        "registry_federation": registry.get("registry_federation", {"enabled": False, "peers": []}),
        "eligible_stakeholders": {"count": len(stakeholders), "weight": total_weight},
        "thresholds": {
            "quorum_ratio": quorum_ratio,
            "pass_ratio": pass_ratio,
            "quorum_weight": quorum_threshold,
            "pass_weight": pass_threshold,
        },
    }

    policy_resolution_path = out_dir / "policy_resolution.json"
    write_json(policy_resolution_path, resolution)

    tally = {
        "schema": "tally_v1",
        "election_id": election_id,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "stakeholder_scope": scope,
        "mvss_policy_ref": policy.get("policy_id", "unknown"),
        "registry_snapshot_ref": registry.get("snapshot_id", "unknown"),
        "registry_federation": registry.get("registry_federation", {"enabled": False, "peers": []}),
        "policy_resolution_ref": str(policy_resolution_path.name),
        "totals": totals,
        "quorum_threshold": quorum_threshold,
        "pass_threshold": pass_threshold,
    }

    yes_weight = totals.get("yes", {}).get("weight", 0)
    decision_value = "pass" if yes_weight >= pass_threshold and total_weight >= quorum_threshold else "fail"

    decision = {
        "schema": "decision_v1",
        "decision_id": f"decision_{election_id}",
        "election_id": election_id,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "stakeholder_scope": scope,
        "mvss_policy_ref": policy.get("policy_id", "unknown"),
        "registry_snapshot_ref": registry.get("snapshot_id", "unknown"),
        "registry_federation": registry.get("registry_federation", {"enabled": False, "peers": []}),
        "decision": decision_value,
        "decision_proof": {
            "type": "mvss_demo",
            "algorithm": "sha256",
            "tally_hash": make_hash(tally),
        },
        "ledger_anchor": {"type": "placeholder", "anchor_hash": "pending"},
    }

    authorized_actions = []
    if decision_value == "pass":
        authorized_actions = [
            {"action": "apply_governance_bundle", "target": "sophia_run", "scope": scope, "constraints": []}
        ]

    warrant = {
        "schema": "warrant_v1",
        "warrant_id": f"warrant_{election_id}",
        "decision_id": decision["decision_id"],
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "stakeholder_scope": scope,
        "mvss_policy_ref": policy.get("policy_id", "unknown"),
        "registry_snapshot_ref": registry.get("snapshot_id", "unknown"),
        "registry_federation": registry.get("registry_federation", {"enabled": False, "peers": []}),
        "authorized_actions": authorized_actions,
    }

    validate(SCHEMA_DIR / "registry_snapshot.schema.json", registry)
    validate(SCHEMA_DIR / "mvss_policy.schema.json", policy)
    validate(SCHEMA_DIR / "election.schema.json", election)
    validate(SCHEMA_DIR / "tally.schema.json", tally)
    validate(SCHEMA_DIR / "decision.schema.json", decision)
    validate(SCHEMA_DIR / "warrant.schema.json", warrant)

    write_json(out_dir / "election.json", election)
    write_json(out_dir / "tally.json", tally)
    write_json(out_dir / "decision.json", decision)
    write_json(out_dir / "warrant.json", warrant)

    print("[mint_governance_bundle] OK wrote election/tally/decision/warrant + policy_resolution.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
