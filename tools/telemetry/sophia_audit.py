#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List

from jsonschema import Draft202012Validator


def load_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True, help="Run directory containing telemetry.json and epistemic_graph.json")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--diff-report", default="", help="Optional guidance_diff report.json")
    ap.add_argument("--schema", default="schema/sophia_audit.schema.json")
    ap.add_argument("--out", default="", help="Output path (default: <run-dir>/sophia_audit.json)")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    run_dir = Path(args.run_dir).resolve()

    tele = load_json(run_dir / "telemetry.json")
    graph = load_json(run_dir / "epistemic_graph.json")

    # Build artifact set from graph nodes
    artifacts = set()
    for n in graph.get("nodes", []):
        if n.get("kind") == "artifact":
            p = (n.get("data") or {}).get("path")
            if p:
                artifacts.add(str(p).replace("\\", "/"))

    findings: List[Dict[str, Any]] = []
    repairs: List[Dict[str, Any]] = []

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

    # Decision
    decision = "pass"
    if any(f["severity"] == "fail" for f in findings):
        decision = "fail"
    elif any(f["severity"] == "warn" for f in findings):
        decision = "warn"

    report = {
        "schema": "sophia_audit_v1",
        "run_id": tele.get("run_id", run_dir.name),
        "decision": decision,
        "summary": f"Sophia audit complete: {decision}. Findings={len(findings)} Repairs={len(repairs)}",
        "findings": findings,
        "repairs": repairs
    }

    outp = Path(args.out) if args.out else (run_dir / "sophia_audit.json")
    outp.write_text(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")

    # Validate schema
    schema = load_json(repo / args.schema)
    Draft202012Validator(schema).validate(report)

    print(f"[sophia_audit] OK wrote {outp} decision={decision}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
