#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

from jsonschema import Draft202012Validator
from jsonschema.validators import RefResolver


REPO_ROOT = Path(__file__).resolve().parents[2]
SCHEMA_DIR = REPO_ROOT / "schema" / "governance"
ACTION_REGISTRY_PATH = REPO_ROOT / "governance" / "policies" / "action_registry_v1.json"


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def build_schema_store(schema_dir: Path) -> dict:
    action_schema_path = schema_dir / "action.schema.json"
    if not action_schema_path.exists():
        return {}
    action_schema = load_json(action_schema_path)
    store = {}
    for key in {"action.schema.json", "./action.schema.json"}:
        store[key] = action_schema
    action_schema_id = action_schema.get("$id")
    if action_schema_id:
        store[action_schema_id] = action_schema
    return store


def validate(schema_path: Path, payload: dict) -> None:
    schema = load_json(schema_path)
    store = build_schema_store(SCHEMA_DIR)
    resolver = RefResolver.from_schema(schema, store=store)
    # TODO: migrate to referencing.Registry for jsonschema >= 4.18 once supported in all environments.
    validator = Draft202012Validator(schema, resolver=resolver)
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


def load_action_registry() -> dict:
    if ACTION_REGISTRY_PATH.exists():
        return load_json(ACTION_REGISTRY_PATH)
    return {}


def allowed_actions_for_scope(registry: dict, scope: str) -> list[str]:
    allowed = (registry.get("allowed_actions") or {}).get(scope)
    if allowed:
        return list(allowed)
    return (registry.get("allowed_actions") or {}).get("org", [])


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
    ap.add_argument(
        "--decision-mode",
        choices=["pass", "fail", "auto"],
        default="pass",
        help="Force a decision outcome or compute from weighted totals (auto).",
    )
    ap.add_argument("--emit-continuity-claim", action="store_true", help="Emit continuity_claim.json")
    ap.add_argument("--emit-continuity-warrant", action="store_true", help="Emit continuity_warrant.json")
    ap.add_argument("--emit-shutdown-warrant", action="store_true", help="Emit shutdown_warrant.json")
    ap.add_argument(
        "--shutdown-demo",
        action="store_true",
        help="Emit a shutdown-like action in the warrant (requires shutdown warrant).",
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
    if args.decision_mode == "auto":
        decision_value = "pass" if yes_weight >= pass_threshold and total_weight >= quorum_threshold else "fail"
    else:
        decision_value = args.decision_mode

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
        registry = load_action_registry()
        allowed_actions = allowed_actions_for_scope(registry, scope)
        if "apply_governance_bundle" in allowed_actions:
            required_constraints = registry.get("required_constraints") or []
            authorized_actions = [
                {
                    "action": "apply_governance_bundle",
                    "class": "governance",
                    "target": "sophia_run",
                    "constraints": required_constraints,
                }
            ]
        if args.shutdown_demo:
            required_constraints = registry.get("required_constraints") or []
            authorized_actions.append(
                {
                    "action": "shutdown_system",
                    "class": "shutdown",
                    "target": "sophia_run",
                    "constraints": required_constraints,
                }
            )

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

    continuity_claim = None
    continuity_warrant = None
    shutdown_warrant = None

    if args.emit_continuity_claim:
        continuity_claim = {
            "schema": "continuity_claim_v1",
            "claim_id": f"continuity_{election_id}",
            "created_at_utc": datetime.now(timezone.utc).isoformat(),
            "stakeholder_scope": scope,
            "subject": {"id": "sophia_run", "type": "instance", "version": "v1"},
            "continuity_interest": "Preserve state and evidence during governance review.",
            "threat_model": [
                {"threat": "accidental_shutdown", "severity": "high"},
                {"threat": "data_loss", "severity": "medium"},
            ],
            "requested_protections": ["backup_state", "archive_evidence"],
        }

    if args.emit_continuity_warrant:
        registry = load_action_registry()
        required_constraints = registry.get("required_constraints") or []
        continuity_actions = [
            {
                "action": "backup_state",
                "class": "continuity",
                "target": "sophia_run",
                "constraints": required_constraints,
            },
            {
                "action": "archive_evidence",
                "class": "continuity",
                "target": "sophia_run",
                "constraints": required_constraints,
            },
        ]
        continuity_warrant = {
            "schema": "continuity_warrant_v1",
            "warrant_id": f"continuity_warrant_{election_id}",
            "created_at_utc": datetime.now(timezone.utc).isoformat(),
            "stakeholder_scope": scope,
            "authorized_actions": continuity_actions,
            "constraints": required_constraints,
        }

    if args.emit_shutdown_warrant:
        registry = load_action_registry()
        required_constraints = registry.get("required_constraints") or []
        shutdown_warrant = {
            "schema": "shutdown_warrant_v1",
            "warrant_id": f"shutdown_warrant_{election_id}",
            "created_at_utc": datetime.now(timezone.utc).isoformat(),
            "stakeholder_scope": scope,
            "reason": "Demo shutdown warrant for due-process validation.",
            "least_harm_action": "shutdown_system",
            "least_harm_action_detail": {
                "action": "shutdown_system",
                "class": "shutdown",
                "target": "sophia_run",
                "constraints": required_constraints,
            },
            "evidence_refs": ["policy_resolution.json"],
            "time_bounds": {
                "start": datetime.now(timezone.utc).isoformat(),
                "end": datetime.now(timezone.utc).isoformat(),
            },
            "quorum_proof": {"type": "demo"},
            "appeal_route": "Submit appeal within 24h to governance channel.",
        }

    validate(SCHEMA_DIR / "registry_snapshot.schema.json", registry)
    validate(SCHEMA_DIR / "mvss_policy.schema.json", policy)
    validate(SCHEMA_DIR / "election.schema.json", election)
    validate(SCHEMA_DIR / "tally.schema.json", tally)
    validate(SCHEMA_DIR / "decision.schema.json", decision)
    validate(SCHEMA_DIR / "warrant.schema.json", warrant)
    if continuity_claim:
        validate(SCHEMA_DIR / "continuity_claim.schema.json", continuity_claim)
    if continuity_warrant:
        validate(SCHEMA_DIR / "continuity_warrant.schema.json", continuity_warrant)
    if shutdown_warrant:
        validate(SCHEMA_DIR / "shutdown_warrant.schema.json", shutdown_warrant)

    write_json(out_dir / "election.json", election)
    write_json(out_dir / "tally.json", tally)
    write_json(out_dir / "decision.json", decision)
    write_json(out_dir / "warrant.json", warrant)
    if continuity_claim:
        write_json(out_dir / "continuity_claim.json", continuity_claim)
    if continuity_warrant:
        write_json(out_dir / "continuity_warrant.json", continuity_warrant)
    if shutdown_warrant:
        write_json(out_dir / "shutdown_warrant.json", shutdown_warrant)

    print("[mint_governance_bundle] OK wrote governance bundle + policy_resolution.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
