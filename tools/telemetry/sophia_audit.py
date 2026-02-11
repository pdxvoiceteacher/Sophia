#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

_run_audit_v3 = None
_run_audit_v2 = None
_run_basic_audit = None
try:
    if importlib.util.find_spec("sophia_core.audit") is not None:
        from sophia_core.audit import run_audit_v3 as _run_audit_v3
        from sophia_core.audit import run_audit_v2 as _run_audit_v2
        from sophia_core.audit import run_basic_audit as _run_basic_audit
except ModuleNotFoundError:
    _run_audit_v3 = None
    _run_audit_v2 = None
    _run_basic_audit = None

from jsonschema import Draft202012Validator
from jsonschema.validators import RefResolver


def load_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))


def save_json(p: Path, payload: dict) -> None:
    p.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )


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


def validate_instance(schema_path: Path, instance: dict) -> list[str]:
    schema = load_json(schema_path)
    store = build_schema_store(schema_path.parent)
    resolver = RefResolver.from_schema(schema, store=store)
    # TODO: migrate to referencing.Registry for jsonschema >= 4.18 once supported in all environments.
    validator = Draft202012Validator(schema, resolver=resolver)
    return [f"{list(err.path)} {err.message}" for err in validator.iter_errors(instance)]


def extract_governance_summary(election: dict | None, tally: dict | None, decision: dict | None) -> dict:
    summary = {
        "election_present": bool(election),
        "tally_present": bool(tally),
        "decision_present": bool(decision),
    }
    if election:
        summary["stakeholder_scope"] = election.get("stakeholder_scope")
        summary["mvss_policy_ref"] = election.get("mvss_policy_ref")
    if tally:
        summary["quorum_threshold"] = tally.get("quorum_threshold")
        summary["pass_threshold"] = tally.get("pass_threshold")
        summary["policy_resolution_ref"] = tally.get("policy_resolution_ref")
    if decision:
        summary["decision"] = decision.get("decision")
    return summary


def load_action_registry(repo: Path) -> dict | None:
    registry_path = repo / "governance" / "policies" / "action_registry_v1.json"
    if registry_path.exists():
        return load_json(registry_path)
    return None


def validate_actions(
    findings: list[dict],
    action_registry: dict,
    actions: list[dict],
    scope: str,
    id_prefix: str,
    severity: str = "warn",
    require_registry: bool = False,
) -> None:
    allowed_actions = (action_registry.get("allowed_actions") or {}).get(scope)
    if allowed_actions is None:
        allowed_actions = (action_registry.get("allowed_actions") or {}).get("org", [])
    forbidden_classes = set(action_registry.get("forbidden_classes") or [])
    required_constraints = set(action_registry.get("required_constraints") or [])
    if require_registry and not allowed_actions:
        findings.append(
            {
                "id": f"{id_prefix}_allowlist_missing",
                "severity": "fail",
                "type": "governance_action_registry_missing",
                "message": f"Action registry does not define allowed_actions for scope '{scope}'.",
                "data": {"scope": scope},
            }
        )
    for action in actions:
        action_name = action.get("action", "")
        action_class = action.get("class") or action.get("classification")
        if allowed_actions and action_name not in allowed_actions:
            findings.append(
                {
                    "id": f"{id_prefix}_action_not_allowed_{action_name}",
                    "severity": severity,
                    "type": "governance_action_not_allowed",
                    "message": f"Action '{action_name}' is not allowed for scope.",
                    "data": {"action": action_name, "scope": scope},
                }
            )
        if require_registry and not allowed_actions:
            findings.append(
                {
                    "id": f"{id_prefix}_action_registry_empty_{action_name}",
                    "severity": "fail",
                    "type": "governance_action_registry_missing",
                    "message": "Action registry missing allowlist; continuity actions are not permitted.",
                    "data": {"action": action_name, "scope": scope},
                }
            )
        if action_class and action_class in forbidden_classes:
            findings.append(
                {
                    "id": f"{id_prefix}_action_forbidden_{action_name}",
                    "severity": "fail",
                    "type": "governance_action_forbidden",
                    "message": f"Action '{action_name}' uses forbidden class '{action_class}'.",
                    "data": {"action": action_name, "classification": action_class},
                }
            )
        constraints = set(action.get("constraints") or [])
        missing_constraints = sorted(required_constraints - constraints)
        if missing_constraints:
            findings.append(
                {
                    "id": f"{id_prefix}_action_missing_constraints_{action_name}",
                    "severity": severity,
                    "type": "governance_action_missing_constraints",
                    "message": f"Action '{action_name}' missing constraints: {', '.join(missing_constraints)}.",
                    "data": {"action": action_name, "missing_constraints": missing_constraints},
                }
            )


def is_shutdown_like(action_name: str) -> bool:
    lowered = action_name.lower()
    return any(token in lowered for token in ("shutdown", "terminate", "decommission"))


def shutdown_warrant_missing_fields(shutdown_warrant: dict) -> list[str]:
    missing: list[str] = []
    time_bounds = shutdown_warrant.get("time_bounds") or {}
    if not time_bounds or not time_bounds.get("start") or not time_bounds.get("end"):
        missing.append("time_bounds.start/end")
    if not shutdown_warrant.get("least_harm_action"):
        missing.append("least_harm_action")
    if not shutdown_warrant.get("least_harm_action_detail"):
        missing.append("least_harm_action_detail")
    quorum_proof = shutdown_warrant.get("quorum_proof")
    if not isinstance(quorum_proof, dict) or not quorum_proof:
        missing.append("quorum_proof")
    if not shutdown_warrant.get("appeal_route"):
        missing.append("appeal_route")
    return missing






def load_sensitive_action_registry(repo: Path) -> dict:
    path = repo / "config" / "sensitive_action_registry_v1.json"
    if not path.exists():
        return {
            "sensitive_tokens": ["control", "override", "shutdown", "terminate", "coercive"],
            "sensitive_actions": [],
            "source": "builtin_default",
        }
    payload = load_json(path)
    payload["source"] = str(path)
    return payload


def is_sensitive_action(action_name: str, registry: dict | None = None) -> bool:
    lowered = action_name.lower()
    reg = registry or {}
    exact_actions = {str(item).lower() for item in reg.get("sensitive_actions") or []}
    if lowered in exact_actions:
        return True
    tokens = tuple(str(item).lower() for item in (reg.get("sensitive_tokens") or []))
    if not tokens:
        tokens = ("control", "override", "shutdown", "terminate", "coercive")
    return any(token in lowered for token in tokens)

def load_sentinel_state(run_dir: Path) -> dict | None:
    path = run_dir / "sentinel_state.json"
    if not path.exists():
        return None
    return load_json(path)

def load_repair_targets(repo: Path) -> dict:
    targets_path = repo / "sophia-core" / "config" / "repair_targets.json"
    if not targets_path.exists():
        return {}
    return load_json(targets_path)


def map_repair_target(finding_type: str, repair_targets: dict) -> dict:
    target = repair_targets.get(finding_type, {})
    if target:
        return {
            "target_module": target.get("target_module", "unmapped"),
            "target_file": target.get("target_file", "unmapped"),
            "suggested_knob": target.get("suggested_knob"),
            "action": target.get("action"),
        }
    return {
        "target_module": "unmapped",
        "target_file": "unmapped",
        "suggested_knob": None,
        "action": None,
    }


def build_contradiction_clusters(claims: list[dict]) -> list[dict]:
    clusters: list[dict] = []
    numeric_pattern = re.compile(r"(?P<key>[A-Za-z0-9_.-]+)\s*[:=]\s*(?P<value>-?\d+(?:\.\d+)?)")
    year_pattern = re.compile(r"\b(19\d{2}|20\d{2})\b")
    causal_pattern = re.compile(
        r"(?P<cause>[A-Za-z0-9_./\\ -]+?)\s+(causes|leads to|drives)\s+(?P<effect>[A-Za-z0-9_./\\ -]+)"
    )

    numeric_values: dict[str, dict[str, list[str]]] = {}
    temporal_values: dict[str, dict[str, list[str]]] = {}
    causal_edges: dict[tuple[str, str], list[str]] = {}

    for claim in claims:
        claim_id = str(claim.get("id", "unknown"))
        statement = str(claim.get("statement", "")) or str(claim.get("notes", ""))
        statement_lc = statement.lower()

        for match in numeric_pattern.finditer(statement):
            key = match.group("key").lower()
            value = match.group("value")
            numeric_values.setdefault(key, {}).setdefault(value, []).append(claim_id)

        years = year_pattern.findall(statement)
        if years:
            time_key = str(claim.get("key") or claim.get("id") or statement[:32]).lower()
            for year in years:
                temporal_values.setdefault(time_key, {}).setdefault(year, []).append(claim_id)

        if claim.get("type") == "causal" or "causes" in statement_lc or "leads to" in statement_lc:
            confidence = float(claim.get("confidence", 0.0))
            if confidence >= 0.7:
                causal_match = causal_pattern.search(statement_lc)
                if causal_match:
                    cause = causal_match.group("cause").strip()
                    effect = causal_match.group("effect").strip()
                    causal_edges.setdefault((cause, effect), []).append(claim_id)

    for key, value_map in numeric_values.items():
        if len(value_map) > 1:
            claims_involved = sorted({cid for ids in value_map.values() for cid in ids})
            clusters.append(
                {
                    "type": "numeric",
                    "key": key,
                    "claims_involved": claims_involved,
                    "why": f"Conflicting numeric values for {key}: {sorted(value_map.keys())}.",
                }
            )

    for key, year_map in temporal_values.items():
        if len(year_map) > 1:
            claims_involved = sorted({cid for ids in year_map.values() for cid in ids})
            clusters.append(
                {
                    "type": "temporal",
                    "key": key,
                    "claims_involved": claims_involved,
                    "why": f"Multiple timestamps for {key}: {sorted(year_map.keys())}.",
                }
            )

    for (cause, effect), claim_ids in causal_edges.items():
        reversed_ids = causal_edges.get((effect, cause))
        if reversed_ids:
            clusters.append(
                {
                    "type": "causal",
                    "key": f"{cause}↔{effect}",
                    "claims_involved": sorted(set(claim_ids + reversed_ids)),
                    "why": f"Conflicting causal direction between '{cause}' and '{effect}'.",
                }
            )

    return clusters


def apply_noise_suppression(findings: list[dict], history_path: Path, threshold: float = 0.6) -> list[dict]:
    stats = {"total_runs": 0, "findings": {}}
    if history_path.exists():
        stats = load_json(history_path)

    total_runs = int(stats.get("total_runs", 0))
    type_counts = stats.get("findings", {})
    unique_types = {f["type"] for f in findings}
    noise_adjustments: list[dict] = []
    corroborated = len(unique_types) > 1

    for finding in findings:
        if finding["severity"] != "warn":
            continue
        ftype = finding["type"]
        rate = 0.0
        if total_runs > 0:
            rate = float(type_counts.get(ftype, 0)) / float(total_runs)
        if rate > threshold and not corroborated:
            finding["severity"] = "info"
            noise_adjustments.append(
                {
                    "finding_type": ftype,
                    "prior_rate": round(rate, 3),
                    "action": "downgraded_to_info",
                    "reason": "detector_fires_frequently_without_corroboration",
                }
            )

    updated_types = {f["type"] for f in findings}
    stats["total_runs"] = total_runs + 1
    stats.setdefault("findings", {})
    for ftype in updated_types:
        stats["findings"][ftype] = int(stats["findings"].get(ftype, 0)) + 1

    history_path.parent.mkdir(parents=True, exist_ok=True)
    save_json(history_path, stats)
    return noise_adjustments




def load_epoch_summary(run_dir: Path) -> dict:
    epoch_path = run_dir / "epoch.json"
    metrics_path = run_dir / "epoch_metrics.json"
    findings_path = run_dir / "epoch_findings.json"
    if not (epoch_path.exists() and metrics_path.exists() and findings_path.exists()):
        return {}
    epoch = load_json(epoch_path)
    metrics = load_json(metrics_path)
    findings_payload = load_json(findings_path)
    findings = findings_payload.get("findings") or []
    kinds = {}
    for f in findings:
        kind = f.get("kind", "unknown")
        kinds[kind] = kinds.get(kind, 0) + 1
    series = metrics.get("step_series") or []
    max_delta_psi = 0.0
    prev = None
    for row in series:
        psi = float(row.get("Psi", 0.0))
        if prev is not None:
            max_delta_psi = max(max_delta_psi, abs(psi - prev))
        prev = psi
    return {
        "epoch_id": epoch.get("epoch_id"),
        "run_mode": epoch.get("run_mode"),
        "prompt_hash": epoch.get("prompt_hash"),
        "finding_counts": kinds,
        "max_delta_psi": max_delta_psi,
        "branch_analysis": findings_payload.get("analysis", {}).get("branch", {}),
        "disclaimer": findings_payload.get("disclaimer", "Behavioral test signals only; does not imply consciousness."),
    }


def load_metric_registry(repo: Path) -> dict:
    path = repo / "config" / "metric_registry_v1.json"
    if not path.exists():
        return {"schema": "metric_registry_v1", "metrics": {}}
    return load_json(path)


def load_detector_registry(repo: Path) -> dict:
    path = repo / "config" / "detector_registry_v1.json"
    if not path.exists():
        return {"schema": "detector_registry_v1", "detectors": {}}
    return load_json(path)


def build_definition_provenance(run_dir: Path, tele: dict, repo: Path) -> dict:
    metric_registry = load_metric_registry(repo)
    detector_registry = load_detector_registry(repo)
    epoch_findings_path = run_dir / "epoch_findings.json"
    epoch_findings = load_json(epoch_findings_path) if epoch_findings_path.exists() else {}
    detectors_used = ((epoch_findings.get("analysis") or {}).get("detectors_used") or {}) if isinstance(epoch_findings, dict) else {}

    metrics = tele.get("metrics") or {}
    metric_provenance = {
        "TEL": {"provenance_source": "tel.json + tel_events.jsonl", "artifact_hashes": True},
        "E": {"proxy": "telemetry.metrics.E", "estimator": "declared_proxy"},
        "T": {"proxy": "telemetry.metrics.T"},
        "Psi": {"formula": "E*T"},
        "DeltaS": {"proxy": "telemetry.metrics.DeltaS", "mode": "surrogate"},
        "Lambda": {"detector": "registry_declared", "thresholds": detectors_used.get("branch_divergence", {}).get("parameters", {})},
        "Es": {"test_suite": "epoch_step_invariance_proxy"},
    }
    if "DeltaS_mode" in metrics:
        metric_provenance["DeltaS"]["mode"] = metrics.get("DeltaS_mode")

    missing = []
    for metric, rule in metric_registry.get("metrics", {}).items():
        mp = metric_provenance.get(metric, {})
        for field in rule.get("required_fields", []):
            if field not in mp:
                missing.append(f"{metric}:{field}")

    return {
        "metric_registry": metric_registry.get("schema", "metric_registry_v1"),
        "detector_registry": detector_registry.get("schema", "detector_registry_v1"),
        "metric_provenance": metric_provenance,
        "detectors_used": detectors_used,
        "missing_required_fields": missing,
        "deltaS_mode": metric_provenance.get("DeltaS", {}).get("mode", "surrogate"),
    }

def compute_risk_score(
    findings: list[dict],
    contradiction_clusters: list[dict],
    ethical_symmetry: Any,
    memory_drift_flag: bool,
    epoch_summary: dict | None = None,
) -> tuple[int, dict]:
    counts = {
        "missing_evidence": sum(1 for f in findings if f["type"] == "missing_evidence"),
        "missing_counterevidence": sum(1 for f in findings if f["type"] == "missing_counterevidence"),
        "coherence_regression": sum(
            1
            for f in findings
            if f["type"] in ("telemetry_regression_risk", "coherence_regression", "coherence_drift")
        ),
        "contradictions": len(contradiction_clusters),
    }
    ethics_breach = ethical_symmetry is not None and isinstance(ethical_symmetry, (int, float)) and ethical_symmetry < 0.5

    evidence_integrity = min(40, counts["missing_evidence"] * 20 + counts["missing_counterevidence"] * 10)
    coherence_drift = min(25, counts["coherence_regression"] * 12 + (15 if memory_drift_flag else 0))
    contradiction_risk = min(20, counts["contradictions"] * 10)
    ethics_risk = 15 if ethics_breach else 0

    epoch_counts = (epoch_summary or {}).get("finding_counts", {})
    epoch_risk = min(20, int(epoch_counts.get("teleport_violation", 0)) * 10 + int(epoch_counts.get("branch_divergence", 0)) * 6 + int(epoch_counts.get("entropy_spike", 0)) * 4 + int(epoch_counts.get("ethical_symmetry_drop", 0)) * 4)

    risk_score = min(100, evidence_integrity + coherence_drift + contradiction_risk + ethics_risk + epoch_risk)
    components = {
        "evidence_integrity": evidence_integrity,
        "coherence_drift": coherence_drift,
        "contradiction_risk": contradiction_risk,
        "ethics_symmetry": ethics_risk,
        "counts": counts,
        "memory_drift": bool(memory_drift_flag),
        "ethical_symmetry_breach": bool(ethics_breach),
        "epoch_behavioral": epoch_risk,
    }
    return risk_score, components


def build_plan(
    run_id: str,
    decision: str,
    findings: list[dict],
    risk_score: int,
    repair_targets: dict,
) -> dict:
    severity_rank = {"fail": 2, "warn": 1, "info": 0}
    sorted_findings = sorted(
        findings,
        key=lambda f: (severity_rank.get(f["severity"], 0), f["type"]),
        reverse=True,
    )
    top_risks = [
        {
            "id": f["id"],
            "type": f["type"],
            "severity": f["severity"],
            "summary": f["message"],
        }
        for f in sorted_findings[:3]
    ]

    recommended_actions = []
    for finding in sorted_findings[:5]:
        target = map_repair_target(finding["type"], repair_targets)
        priority = "low"
        if finding["severity"] == "warn":
            priority = "medium"
        if finding["severity"] == "fail":
            priority = "high"
        action_text = target.get("action") or f"Address {finding['type']} finding."
        target_label = target.get("target_file") if target.get("target_file") != "unmapped" else target.get("target_module")
        recommended_actions.append(
            {
                "action": action_text,
                "target": target_label,
                "priority": priority,
                "proof": {
                    "finding_id": finding["id"],
                    "finding_type": finding["type"],
                },
            }
        )

    next_experiments = []
    if decision in ("warn", "fail"):
        next_experiments.append(
            {
                "id": "exp_review_findings",
                "why": "Investigate high-risk findings and validate remediation impacts.",
                "expected_signal": "Lower risk_score and reduced finding count on rerun.",
            }
        )

    return {
        "schema": "sophia_plan_v1",
        "run_id": run_id,
        "decision": decision,
        "risk_score": risk_score,
        "top_risks": top_risks,
        "recommended_actions": recommended_actions,
        "next_experiments": next_experiments,
    }


def load_anchor_report(repo: Path):
    anchor_path = repo / "tools" / "telemetry" / "blockchain_anchor.py"
    spec = importlib.util.spec_from_file_location("sophia_blockchain_anchor", anchor_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Unable to load blockchain anchor module from {anchor_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if not hasattr(module, "anchor_report"):
        raise AttributeError("anchor_report not found in blockchain_anchor module")
    return module.anchor_report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True, help="Run directory containing telemetry.json and epistemic_graph.json")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--diff-report", default="", help="Optional guidance_diff report.json")
    ap.add_argument("--schema", default="schema/sophia_audit.schema.json")
    ap.add_argument(
        "--audit-sophia",
        action="store_true",
        help="Emit Sophia TEL events to <run-dir>/ucc_tel_events.jsonl.",
    )
    ap.add_argument("--audit-config", default="", help="Optional Sophia audit config JSON path.")
    ap.add_argument("--blockchain-commit", action="store_true", help="Anchor the audit report hash to a ledger.")
    ap.add_argument("--calibrate-trajectories", action="store_true", help="Enable trajectory phase checks.")
    ap.add_argument("--ethics-check", action="store_true", help="Enable ethical symmetry checks.")
    ap.add_argument("--memory-aware", action="store_true", help="Enable causal memory drift checks.")
    ap.add_argument(
        "--mode",
        default="ci",
        choices=["ci", "research"],
        help="Audit mode: ci (minimal, deterministic) or research (expanded checks).",
    )
    ap.add_argument("--out", default="", help="Output path (default: <run-dir>/sophia_audit.json)")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    run_dir = Path(args.run_dir).resolve()
    run_basic_audit = _run_basic_audit
    run_audit_v2 = _run_audit_v2
    run_audit_v3 = _run_audit_v3
    repair_targets = load_repair_targets(repo)

    if run_basic_audit is None:
        sophia_src = repo / "sophia-core" / "src"
        if sophia_src.exists():
            import sys

            sys.path.insert(0, str(sophia_src))
            try:
                if importlib.util.find_spec("sophia_core.audit") is not None:
                    module = importlib.import_module("sophia_core.audit")
                    run_audit_v3 = getattr(module, "run_audit_v3", None)
                    run_audit_v2 = getattr(module, "run_audit_v2", None)
                    run_basic_audit = getattr(module, "run_basic_audit", None)
                else:
                    run_audit_v3 = None
                    run_audit_v2 = None
                    run_basic_audit = None
            except ModuleNotFoundError:
                run_audit_v3 = None
                run_audit_v2 = None
                run_basic_audit = None

    tele = load_json(run_dir / "telemetry.json")
    graph_path = run_dir / "epistemic_graph.json"
    if not graph_path.exists():
        subprocess.run(
            [
                sys.executable,
                str(repo / "tools" / "telemetry" / "build_epistemic_graph.py"),
                "--run-dir",
                str(run_dir),
                "--repo-root",
                str(repo),
            ],
            check=True,
        )
    graph = load_json(graph_path)

    if args.audit_sophia:
        os.environ.setdefault("UCC_TEL_EVENTS_OUT", str(run_dir / "ucc_tel_events.jsonl"))

    # Build artifact set from graph nodes
    artifacts = set()
    for n in graph.get("nodes", []):
        if n.get("kind") == "artifact":
            p = (n.get("data") or {}).get("path")
            if p:
                artifacts.add(str(p).replace("\\", "/"))

    findings: List[Dict[str, Any]] = []
    repairs: List[Dict[str, Any]] = []
    trend_summary: Dict[str, Any] = {}
    contradictions: List[Dict[str, Any]] = []
    repair_suggestions: List[Dict[str, Any]] = []
    metrics_snapshot: Dict[str, Any] = {}
    trajectory_phase = "unknown"
    ethical_symmetry: Any = None
    memory_kernel: Dict[str, Any] = {}
    memory_drift_flag = False
    blockchain_anchor_hash = None

    audit_config_path = Path(args.audit_config).resolve() if args.audit_config else None

    schema_name = Path(args.schema).name
    if "v3" in schema_name:
        schema_id = "sophia_audit_v3"
    elif "v2" in schema_name:
        schema_id = "sophia_audit_v2"
    else:
        schema_id = "sophia_audit_v1"

    if run_audit_v3 is not None and schema_id == "sophia_audit_v3":
        audit = run_audit_v3(
            tele,
            graph,
            repo_root=repo,
            audit_config_path=audit_config_path,
            tel_hook=None,
            emit_repair_events=args.audit_sophia,
            calibrate_trajectories=args.calibrate_trajectories,
            ethics_check=args.ethics_check,
            memory_aware=args.memory_aware,
        )
        findings = [
            {
                "id": f.id,
                "severity": f.severity,
                "type": f.type,
                "message": f.message,
                "data": f.data,
            }
            for f in audit.findings
        ]
        repairs = [
            {
                "id": r.id,
                "priority": r.priority,
                "action": r.action,
                "details": r.details,
            }
            for r in audit.repairs
        ]
        trend_summary = audit.trend_summary
        contradictions = [
            {"statements": c.statements, "kind": c.kind, "key": c.key} for c in audit.contradictions
        ]
        repair_suggestions = [
            {
                "id": s.id,
                "priority": s.priority,
                "suggestion": s.suggestion,
                "reason": s.reason,
                "target_module": s.target_module,
                "target_file": s.target_file,
                "justification": s.justification,
            }
            for s in audit.repair_suggestions
        ]
        metrics_snapshot = audit.metrics_snapshot
        trajectory_phase = audit.trajectory_phase
        ethical_symmetry = audit.ethical_symmetry
        memory_kernel = audit.memory_kernel
        memory_drift_flag = audit.memory_drift_flag
    elif run_audit_v2 is not None and schema_id == "sophia_audit_v2":
        audit = run_audit_v2(
            tele,
            graph,
            repo_root=repo,
            audit_config_path=audit_config_path,
            tel_hook=None,
            emit_repair_events=args.audit_sophia,
        )
        findings = [
            {
                "id": f.id,
                "severity": f.severity,
                "type": f.type,
                "message": f.message,
                "data": f.data,
            }
            for f in audit.findings
        ]
        repairs = [
            {
                "id": r.id,
                "priority": r.priority,
                "action": r.action,
                "details": r.details,
            }
            for r in audit.repairs
        ]
        trend_summary = audit.trend_summary
        contradictions = [
            {"statements": c.statements, "kind": c.kind, "key": c.key} for c in audit.contradictions
        ]
        repair_suggestions = [
            {
                "id": s.id,
                "priority": s.priority,
                "suggestion": s.suggestion,
                "reason": s.reason,
                "target_module": s.target_module,
                "target_file": s.target_file,
                "justification": s.justification,
            }
            for s in audit.repair_suggestions
        ]
    elif run_basic_audit is not None:
        audit = run_basic_audit(tele, graph)
        findings = [
            {
                "id": f.id,
                "severity": f.severity,
                "type": f.type,
                "message": f.message,
                "data": f.data,
            }
            for f in audit.findings
        ]
        repairs = [
            {
                "id": r.id,
                "priority": r.priority,
                "action": r.action,
                "details": r.details,
            }
            for r in audit.repairs
        ]
    else:
        claims = tele.get("claims") or []

        # 1) Evidence integrity
        for c in claims:
            cid = c.get("id", "unknown")
            for ev in c.get("evidence", []) or []:
                evp = str(ev).replace("\\", "/")
                if evp not in artifacts:
                    findings.append({
                        "id": f"finding_missing_evidence_{cid}",
                        "severity": "fail",
                        "type": "missing_evidence",
                        "message": f"Claim {cid} references evidence not present in graph artifacts: {evp}",
                        "data": {"claim_id": cid, "evidence": evp}
                    })
                    repairs.append({
                        "id": f"repair_add_artifact_{cid}",
                        "priority": "high",
                        "action": "Ensure evidence paths are included in telemetry.artifacts and epistemic graph artifact nodes.",
                        "details": {"missing_evidence": evp}
                    })

        # 2) Counterevidence expectation
        for c in claims:
            ctype = c.get("type")
            conf = float(c.get("confidence", 0.0))
            if ctype in ("causal", "predictive") and conf >= 0.7:
                if not (c.get("counterevidence") or []):
                    cid = c.get("id", "unknown")
                    findings.append({
                        "id": f"finding_missing_counter_{cid}",
                        "severity": "warn",
                        "type": "missing_counterevidence",
                        "message": f"Claim {cid} is {ctype} with confidence {conf:.2f} but has no counterevidence listed.",
                        "data": {"claim_id": cid, "confidence": conf}
                    })
                    repairs.append({
                        "id": f"repair_add_counter_{cid}",
                        "priority": "medium",
                        "action": "Add at least one counterevidence path or reduce confidence / add assumptions.",
                        "details": {"claim_id": cid}
                    })

    contradiction_clusters = build_contradiction_clusters(tele.get("claims", []))
    if schema_id in ("sophia_audit_v2", "sophia_audit_v3") and contradiction_clusters:
        for idx, cluster in enumerate(contradiction_clusters, start=1):
            findings.append(
                {
                    "id": f"finding_contradiction_{idx}",
                    "severity": "warn",
                    "type": "contradiction",
                    "message": cluster["why"],
                    "data": cluster,
                }
            )
            contradictions.append(
                {
                    "statements": cluster["claims_involved"],
                    "kind": cluster["type"],
                    "key": cluster.get("key", ""),
                }
            )

    # 3) Optional guidance diff tradeoff warning
    if args.diff_report:
        dr = load_json(Path(args.diff_report))
        d = dr.get("deltas", {})
        dPsi = float(d.get("Psi", 0.0))
        dLam = float(d.get("Lambda", 0.0))
        dDS = float(d.get("DeltaS", 0.0))
        if (dLam > 0 or dDS > 0) and abs(dPsi) < 1e-4:
            findings.append({
                "id": "finding_guidance_tradeoff",
                "severity": "warn",
                "type": "telemetry_regression_risk",
                "message": "Guided run increased DeltaS/Lambda while Psi gain is small; consider whether guidance adds instability.",
                "data": {"dPsi": dPsi, "dLambda": dLam, "dDeltaS": dDS}
            })
            repairs.append({
                "id": "repair_review_guidance",
                "priority": "medium",
                "action": "Review guidance knobs; prefer changes that do not increase DeltaS/Lambda unless Psi gain justifies tradeoff.",
                "details": None
            })

    epoch_summary = load_epoch_summary(run_dir)
    if epoch_summary:
        trend_summary.setdefault("epoch_summary", {}).update(epoch_summary)

    definition_provenance = build_definition_provenance(run_dir, tele, repo)
    trend_summary.setdefault("definition_provenance", {}).update(definition_provenance)

    risk_score, risk_components = compute_risk_score(
        findings,
        contradiction_clusters,
        ethical_symmetry,
        memory_drift_flag,
        epoch_summary=epoch_summary or None,
    )
    metrics_snapshot.setdefault("risk_score", risk_score)
    metrics_snapshot.setdefault("risk_components", risk_components)

    governance_paths = {
        "election": run_dir / "election.json",
        "tally": run_dir / "tally.json",
        "decision": run_dir / "decision.json",
        "warrant": run_dir / "warrant.json",
        "continuity_claim": run_dir / "continuity_claim.json",
        "continuity_warrant": run_dir / "continuity_warrant.json",
        "shutdown_warrant": run_dir / "shutdown_warrant.json",
    }
    governance = {
        name: load_json(path) if path.exists() else None
        for name, path in governance_paths.items()
    }
    sentinel_state = load_sentinel_state(run_dir)
    sensitive_registry = load_sensitive_action_registry(repo)
    if any(governance.values()):
        schema_dir = repo / "schema" / "governance"
        schema_map = {
            "election": schema_dir / "election.schema.json",
            "tally": schema_dir / "tally.schema.json",
            "decision": schema_dir / "decision.schema.json",
            "warrant": schema_dir / "warrant.schema.json",
            "continuity_claim": schema_dir / "continuity_claim.schema.json",
            "continuity_warrant": schema_dir / "continuity_warrant.schema.json",
            "shutdown_warrant": schema_dir / "shutdown_warrant.schema.json",
        }
        for key, instance in governance.items():
            if instance:
                schema_path = schema_map[key]
                if not schema_path.exists():
                    findings.append(
                        {
                            "id": f"finding_governance_schema_missing_{key}",
                            "severity": "warn",
                            "type": "governance_schema_missing",
                            "message": f"Missing governance schema for {key}: {schema_path}",
                            "data": {"artifact": key, "schema": str(schema_path)},
                        }
                    )
                    continue
                errors = validate_instance(schema_path, instance)
                for idx, error in enumerate(errors[:5], start=1):
                    findings.append(
                        {
                            "id": f"finding_governance_schema_{key}_{idx}",
                            "severity": "warn",
                            "type": "governance_schema_invalid",
                            "message": f"{key} schema validation issue: {error}",
                            "data": {"artifact": key, "error": error},
                        }
                    )
        election = governance["election"]
        tally = governance["tally"]
        decision_doc = governance["decision"]
        warrant = governance["warrant"]
        continuity_claim = governance["continuity_claim"]
        continuity_warrant = governance["continuity_warrant"]
        shutdown_warrant = governance["shutdown_warrant"]
        if election:
            for idx, ballot in enumerate(election.get("ballots", []), start=1):
                translations = (ballot.get("ballot_text") or {}).get("translations") or {}
                if not translations:
                    findings.append(
                        {
                            "id": f"finding_governance_missing_translations_{idx}",
                            "severity": "warn",
                            "type": "governance_missing_translations",
                            "message": "Ballot text is missing translations for language justice requirements.",
                            "data": {"ballot_id": ballot.get("ballot_id")},
                        }
                    )
        if tally and not tally.get("policy_resolution_ref"):
            findings.append(
                {
                    "id": "finding_governance_missing_policy_resolution",
                    "severity": "warn",
                    "type": "governance_missing_policy_resolution",
                    "message": "Tally is missing policy_resolution_ref linking to the MVSS thresholds artifact.",
                    "data": None,
                }
            )
        if decision_doc and not warrant:
            findings.append(
                {
                    "id": "finding_governance_missing_warrant",
                    "severity": "warn",
                    "type": "governance_missing_warrant",
                    "message": "Decision exists without a warrant artifact.",
                    "data": None,
                }
            )
        if decision_doc and warrant:
            actions = warrant.get("authorized_actions", []) or []
            sentinel_level = str((sentinel_state or {}).get("state", "normal"))
            if sentinel_level in {"protect", "quarantine"}:
                sensitive_actions = [a for a in actions if is_sensitive_action(str(a.get("action", "")), sensitive_registry)]
                if sensitive_actions and not warrant.get("governance_warrant"):
                    findings.append(
                        {
                            "id": "finding_sentinel_sensitive_action_requires_warrant",
                            "severity": "fail",
                            "type": "sentinel_sensitive_action_requires_warrant",
                            "message": "Sensitive actions require governance_warrant when sentinel state is protect/quarantine.",
                            "data": {"state": sentinel_level, "actions": [a.get("action") for a in sensitive_actions]},
                        }
                    )
                attestations_path = run_dir / "attestations.json"
                if sensitive_actions and not attestations_path.exists():
                    findings.append(
                        {
                            "id": "finding_sentinel_sensitive_action_requires_attestations",
                            "severity": "fail",
                            "type": "sentinel_sensitive_action_requires_attestations",
                            "message": "Sensitive actions require attestations.json artifact when sentinel state is protect/quarantine.",
                            "data": {"state": sentinel_level},
                        }
                    )
            if actions and decision_doc.get("decision") != "pass":
                findings.append(
                    {
                        "id": "finding_governance_warrant_without_pass",
                        "severity": "warn",
                        "type": "governance_warrant_requires_pass",
                        "message": "Warrant authorizes actions even though the decision is not pass.",
                        "data": {"decision": decision_doc.get("decision")},
                    }
                )
            action_registry = load_action_registry(repo)
            if action_registry:
                scope = decision_doc.get("stakeholder_scope") or "org"
                validate_actions(
                    findings,
                    action_registry,
                    actions,
                    scope,
                    "finding_governance_warrant",
                )
            shutdown_like = any(is_shutdown_like(action.get("action", "")) for action in actions)
            if shutdown_like:
                if not shutdown_warrant:
                    findings.append(
                        {
                            "id": "finding_shutdown_warrant_missing",
                            "severity": "fail",
                            "type": "governance_shutdown_warrant_missing",
                            "message": "Shutdown-like action present without shutdown_warrant.json.",
                            "data": None,
                        }
                    )
                else:
                    missing_fields = shutdown_warrant_missing_fields(shutdown_warrant)
                    if missing_fields:
                        findings.append(
                            {
                                "id": "finding_shutdown_warrant_incomplete",
                                "severity": "fail",
                                "type": "governance_shutdown_warrant_incomplete",
                                "message": "Shutdown warrant missing required due-process fields.",
                                "data": {"missing": missing_fields},
                            }
                        )
        if continuity_warrant:
            continuity_actions = continuity_warrant.get("authorized_actions", []) or []
            action_registry = load_action_registry(repo)
            if action_registry:
                scope = continuity_warrant.get("stakeholder_scope") or "org"
                validate_actions(
                    findings,
                    action_registry,
                    continuity_actions,
                    scope,
                    "finding_governance_continuity",
                    severity="fail",
                    require_registry=True,
                )
            else:
                findings.append(
                    {
                        "id": "finding_continuity_registry_missing",
                        "severity": "fail",
                        "type": "governance_continuity_registry_missing",
                        "message": "Continuity warrant present without an action registry to verify allowed actions.",
                        "data": None,
                    }
                )
        if continuity_claim and not continuity_warrant:
            findings.append(
                {
                    "id": "finding_continuity_warrant_missing",
                    "severity": "warn",
                    "type": "governance_continuity_warrant_missing",
                    "message": "Continuity claim present without continuity_warrant.json.",
                    "data": None,
                }
            )
        governance_summary = extract_governance_summary(election, tally, decision_doc)
        governance_summary["continuity_claim_present"] = bool(continuity_claim)
        governance_summary["continuity_warrant_present"] = bool(continuity_warrant)
        governance_summary["shutdown_warrant_present"] = bool(shutdown_warrant)
        governance_summary["sentinel_state"] = (sentinel_state or {}).get("state", "normal")
        governance_summary["sensitive_action_registry_source"] = sensitive_registry.get("source", "builtin_default")
        trend_summary.setdefault("governance_summary", {}).update(governance_summary)

    noise_adjustments = apply_noise_suppression(
        findings, repo / "runs" / "history" / "finding_stats.json"
    )

    missing_def_fields = trend_summary.get("definition_provenance", {}).get("missing_required_fields", [])
    if missing_def_fields:
        findings.append({
            "id": "finding_definition_provenance_missing_fields",
            "severity": "warn",
            "type": "definition_provenance_missing_fields",
            "message": "Metric provenance is missing required registry fields.",
            "data": {"missing": missing_def_fields},
        })

    if noise_adjustments:
        trend_summary.setdefault("noise_adjustments", [])
        trend_summary["noise_adjustments"].extend(noise_adjustments)

    # Decision
    decision = "pass"
    if any(f["severity"] == "fail" for f in findings):
        decision = "fail"
    elif any(f["severity"] == "warn" for f in findings):
        decision = "warn"

    report = {
        "schema": schema_id,
        "run_id": tele.get("run_id", run_dir.name),
        "decision": decision,
        "summary": f"Sophia audit complete: {decision}. Findings={len(findings)} Repairs={len(repairs)}",
        "findings": findings,
        "repairs": repairs,
    }

    if schema_id == "sophia_audit_v1":
        report["metrics_snapshot"] = metrics_snapshot
        if trend_summary:
            report["trend_summary"] = trend_summary

    if schema_id == "sophia_audit_v2":
        report.update(
            {
                "trend_summary": trend_summary,
                "contradictions": contradictions,
                "repair_suggestions": repair_suggestions,
                "metrics_snapshot": metrics_snapshot,
            }
        )
    if schema_id == "sophia_audit_v3":
        report.update(
            {
                "metrics_snapshot": metrics_snapshot,
                "trend_summary": trend_summary,
                "contradictions": contradictions,
                "repair_suggestions": repair_suggestions,
                "contradiction_clusters": contradiction_clusters,
                "trajectory_phase": trajectory_phase,
                "ethical_symmetry": ethical_symmetry,
                "memory_kernel": memory_kernel,
                "memory_drift_flag": memory_drift_flag,
                "blockchain_anchor_hash": blockchain_anchor_hash,
            }
        )
    if schema_id == "sophia_audit_v2":
        report["contradiction_clusters"] = contradiction_clusters

    outp = Path(args.out) if args.out else (run_dir / "sophia_audit.json")
    if args.blockchain_commit and schema_id == "sophia_audit_v3":
        anchor_report = load_anchor_report(repo)
        ledger_path = repo / "runs" / "history" / "blockchain_anchors.jsonl"
        blockchain_anchor_hash = anchor_report(report, ledger_path)
        report["blockchain_anchor_hash"] = blockchain_anchor_hash

    save_json(outp, report)

    plan = build_plan(report["run_id"], decision, findings, risk_score, repair_targets)
    plan_path = run_dir / "sophia_plan.json"
    save_json(plan_path, plan)

    # Validate schema
    schema = load_json(repo / args.schema)
    Draft202012Validator(schema).validate(report)
    plan_schema = load_json(repo / "schema" / "sophia_plan_v1.schema.json")
    Draft202012Validator(plan_schema).validate(plan)

    print(f"[sophia_audit] OK wrote {outp} decision={decision}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
