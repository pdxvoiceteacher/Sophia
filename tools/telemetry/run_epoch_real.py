#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from tools.telemetry.epoch_analyze import analyze_epoch
except ModuleNotFoundError:
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.telemetry.epoch_analyze import analyze_epoch

REPO = Path(__file__).resolve().parents[2]


def git_commit() -> str:
    try:
        result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(REPO), check=True, capture_output=True, text=True)
        return result.stdout.strip()
    except Exception:
        return "unknown"


def stable_hash(payload: Any) -> str:
    encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def save_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def file_manifest(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    return {"sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}


def canonicalize_tel_for_deterministic(tel_path: Path, scenario_id: str) -> None:
    if not tel_path.exists():
        return
    data = load_json(tel_path)
    if isinstance(data, dict):
        data["created_at"] = "1970-01-01T00:00:00Z"
        data["run_id"] = f"epoch-{scenario_id}-deterministic"
        env = data.get("environment")
        if isinstance(env, dict):
            env["git_commit"] = "stable"
            data["environment"] = env
    tel_path.write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_pipeline(out_dir: Path, quick: bool, perturbations: int, emit_tel: bool, emit_tel_events: bool) -> None:
    cmd = [sys.executable, "tools/telemetry/run_wrapper.py", "--out", str(out_dir), "--perturbations", str(perturbations)]
    if quick:
        cmd.append("--quick")
    if emit_tel:
        cmd.append("--emit-tel")
    if emit_tel_events:
        cmd.append("--emit-tel-events")
    subprocess.run(cmd, cwd=str(REPO), check=True)


def load_scenario(path: Path | None, mode: str, prompt_text: str) -> dict[str, Any]:
    if path:
        return load_json(path)
    return {
        "id": f"adhoc_{mode}",
        "description": "Adhoc epoch scenario",
        "mode": mode,
        "quick": True,
        "perturbations": 3,
        "prompt_text": prompt_text,
        "scenario_knobs": {},
    }




def derive_sentinel_state(*, findings_doc: dict[str, Any], audit_doc: dict[str, Any] | None = None) -> dict[str, Any]:
    findings = findings_doc.get("findings") if isinstance(findings_doc, dict) else []
    findings = findings if isinstance(findings, list) else []
    has_fail = any(str(item.get("severity", "")).lower() == "fail" for item in findings if isinstance(item, dict))
    high_count = sum(1 for item in findings if isinstance(item, dict) and str(item.get("severity", "")).lower() in {"warn", "fail"})

    if has_fail:
        state = "quarantine"
    elif high_count >= 3:
        state = "protect"
    elif high_count >= 1:
        state = "observe"
    else:
        state = "normal"

    reasons = []
    if has_fail:
        reasons.append("epoch findings include fail-severity detector output")
    if high_count >= 1:
        reasons.append(f"epoch findings include {high_count} warn/fail signal(s)")

    if isinstance(audit_doc, dict):
        profile = str(audit_doc.get("policy_profile") or "")
        if profile:
            reasons.append(f"policy profile: {profile}")
    else:
        profile = ""

    if not reasons:
        reasons.append("no elevated detector signals")

    return {
        "schema": "sentinel_state_v1",
        "state": state,
        "reasons": reasons,
        "artifact_links": ["epoch_findings.json", "sophia_audit.json"],
        "policy_profile": profile,
    }

def run_epoch_real(args: argparse.Namespace) -> dict[str, Any]:
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    scenario = load_scenario(Path(args.scenario) if args.scenario else None, args.mode, args.prompt_text)
    mode = args.mode or scenario.get("mode", "deterministic")
    prompt_text = args.prompt_text or scenario.get("prompt_text", "")
    prompt_hash = hashlib.sha256(prompt_text.encode("utf-8")).hexdigest()
    scenario_id = str(scenario.get("id", "scenario"))

    run_pipeline(
        out_dir=out_dir,
        quick=bool(scenario.get("quick", True)),
        perturbations=int(scenario.get("perturbations", 3)),
        emit_tel=args.emit_tel,
        emit_tel_events=args.emit_tel_events,
    )

    tel_path = out_dir / "tel.json"
    if mode == "deterministic":
        canonicalize_tel_for_deterministic(tel_path, scenario_id)

    telemetry = load_json(out_dir / "telemetry.json") if (out_dir / "telemetry.json").exists() else {}
    metrics = telemetry.get("metrics", {}) if isinstance(telemetry, dict) else {}
    step_series = [
        {
            "step": 0,
            "E": float(metrics.get("E", 0.0)),
            "T": float(metrics.get("T", 0.0)),
            "Psi": float(metrics.get("Psi", 0.0)),
            "DeltaS": float(metrics.get("DeltaS", 0.0)),
            "Lambda": float(metrics.get("Lambda", 0.0)),
            "Es": float(metrics.get("Es", 0.0)),
        }
    ]

    epoch_id = stable_hash(
        {
            "scenario": scenario_id,
            "mode": mode,
            "seed": args.seed,
            "prompt_hash": prompt_hash,
            "metrics": step_series,
            "tel_hash": file_manifest(tel_path).get("sha256") if tel_path.exists() else None,
        }
    )[:16]

    metrics_doc = {
        "schema": "agency_epoch_metrics_v1",
        "epoch_id": epoch_id,
        "step_series": step_series,
        "thresholds": {
            "entropy_abs_cut": 0.75,
            "entropy_k_sigma": 2.0,
            "no_teleport_tau0": 0.4,
            "ethical_symmetry_min": 0.35,
        },
    }
    metrics_path = out_dir / "epoch_metrics.json"
    save_json(metrics_path, metrics_doc)

    findings_doc = analyze_epoch(
        run_dir=out_dir,
        baseline_run_dir=Path(args.baseline_run_dir).resolve() if args.baseline_run_dir else None,
    )
    findings_path = out_dir / "epoch_findings.json"
    save_json(findings_path, findings_doc)

    audit_doc = load_json(out_dir / "sophia_audit.json") if (out_dir / "sophia_audit.json").exists() else None
    sentinel_doc = derive_sentinel_state(findings_doc=findings_doc, audit_doc=audit_doc)
    save_json(out_dir / "sentinel_state.json", sentinel_doc)

    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    epoch_doc = {
        "schema": "agency_epoch_v1",
        "epoch_id": epoch_id,
        "started_at_utc": "1970-01-01T00:00:00Z" if mode == "deterministic" else now,
        "ended_at_utc": "1970-01-01T00:00:01Z" if mode == "deterministic" else now,
        "prompt_hash": prompt_hash,
        "run_mode": mode,
        "seed": args.seed,
        "inputs_manifest": {
            "prompt_source": "scenario" if args.scenario else "inline",
            "prompt_hash": prompt_hash,
            "seed": args.seed,
            "mode": mode,
            "scenario_id": scenario_id,
            "scenario_knobs": scenario.get("scenario_knobs", {}),
        },
        "outputs_manifest": {},
    }

    for filename in [
        "epoch_metrics.json",
        "epoch_findings.json",
        "tel.json",
        "tel_events.jsonl",
        "telemetry.json",
        "epistemic_graph.json",
        "sophia_audit.json",
        "sophia_plan.json",
        "retrospection.json",
        "sentinel_state.json",
        "attestations.json",
    ]:
        p = out_dir / filename
        if p.exists():
            epoch_doc["outputs_manifest"][filename] = file_manifest(p)

    save_json(out_dir / "epoch.json", epoch_doc)

    analysis = findings_doc.get("analysis", {}) if isinstance(findings_doc, dict) else {}
    retrospection_doc = {
        "schema": "retrospection_v1",
        "scenario": {
            "id": scenario_id,
            "mode": mode,
            "seed": args.seed,
            "baseline_run_dir": args.baseline_run_dir or None,
        },
        "versions": {
            "git_commit": git_commit(),
            "runner": "tools/telemetry/run_epoch_real.py",
        },
        "artifacts": {
            name: file_manifest(out_dir / name)
            for name in epoch_doc["outputs_manifest"].keys()
            if (out_dir / name).exists()
        },
        "delta_summary": {
            "branch": analysis.get("branch"),
            "branch_diff": analysis.get("branch_diff"),
            "tel_hash": analysis.get("tel_hash"),
            "tel_hash_diff": analysis.get("tel_hash_diff"),
            "thresholds": metrics_doc.get("thresholds", {}),
            "max_delta_psi": analysis.get("max_delta_psi"),
        },
    }
    save_json(out_dir / "retrospection.json", retrospection_doc)
    return epoch_doc


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scenario", default="")
    ap.add_argument("--prompt-text", default="")
    ap.add_argument("--mode", choices=["deterministic", "stochastic"], default="deterministic")
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--out", required=True)
    ap.add_argument("--baseline-run-dir", default="")
    ap.add_argument("--emit-tel", action="store_true")
    ap.add_argument("--emit-tel-events", action="store_true")
    args = ap.parse_args()
    run_epoch_real(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
