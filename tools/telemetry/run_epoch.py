#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import random
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from tools.telemetry.epoch_analyze import analyze_epoch
except ModuleNotFoundError:
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.telemetry.epoch_analyze import analyze_epoch


def stable_hash(payload: Any) -> str:
    encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def read_prompt(args: argparse.Namespace) -> tuple[str, str]:
    if args.prompt_file:
        path = Path(args.prompt_file)
        text = path.read_text(encoding="utf-8-sig")
        return text, f"file:{path.as_posix()}"
    return args.prompt_text, "inline"


def ensure_tel(run_dir: Path, emit_tel: bool, emit_tel_events: bool, series: list[dict[str, Any]], mode: str, run_id: str) -> None:
    if emit_tel:
        payload = {
            "schema": "tel_v1",
            "run_id": run_id,
            "mode": mode,
            "metrics": {
                "steps": len(series),
                "Es_mean": sum(s["Es"] for s in series) / max(1, len(series)),
                "Psi_max": max(s["Psi"] for s in series) if series else 0.0,
            },
        }
        (run_dir / "tel.json").write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if emit_tel_events:
        lines: list[str] = []
        for step in series:
            lines.append(json.dumps({"event": "epoch_step", "step": step["step"], "Es": step["Es"], "Psi": step["Psi"]}))
            if mode == "stochastic" and step["step"] % 3 == 0:
                lines.append(json.dumps({"event": "epoch_branch", "step": step["step"], "branch_id": f"b-{step['step']}"}))
        (run_dir / "tel_events.jsonl").write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")


def file_manifest(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    return {"sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}


def run_epoch(args: argparse.Namespace) -> dict[str, Any]:
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    prompt, source = read_prompt(args)
    prompt_hash = hashlib.sha256(prompt.encode("utf-8")).hexdigest()

    deterministic_key = stable_hash({"prompt_hash": prompt_hash, "seed": args.seed, "mode": args.mode})
    if args.mode == "deterministic":
        rng_seed = int(deterministic_key[:16], 16)
        started_at = "1970-01-01T00:00:00Z"
        ended_at = "1970-01-01T00:00:01Z"
    else:
        nonce = datetime.now(timezone.utc).isoformat()
        rng_seed = int(stable_hash({"deterministic_key": deterministic_key, "nonce": nonce})[:16], 16)
        now = datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
        started_at = now
        ended_at = now

    rng = random.Random(rng_seed)
    steps = 8 if args.mode == "deterministic" else 12
    series: list[dict[str, Any]] = []
    psi = 0.2
    for step in range(steps):
        e_val = round(0.45 + rng.random() * 0.4, 4)
        t_val = round(0.25 + rng.random() * 0.6, 4)
        delta_s = round(0.05 + rng.random() * (0.12 if args.mode == "deterministic" else 0.22), 4)
        lam = round(0.08 + rng.random() * 0.25, 4)
        es = round(max(0.0, 1.0 - (delta_s + lam) / 1.8), 4)
        psi = round(min(1.0, psi + (0.03 + rng.random() * 0.05)), 4)
        series.append({"step": step, "E": e_val, "T": t_val, "Psi": psi, "DeltaS": delta_s, "Lambda": lam, "Es": es})

    epoch_id = stable_hash({"prompt_hash": prompt_hash, "seed": args.seed, "mode": args.mode, "series": series})[:16]
    metrics = {
        "schema": "agency_epoch_metrics_v1",
        "epoch_id": epoch_id,
        "step_series": series,
        "thresholds": {
            "entropy_abs_cut": 0.75,
            "entropy_k_sigma": 2.0,
            "no_teleport_tau0": 0.4,
            "ethical_symmetry_min": 0.35,
        },
    }
    metrics_path = out_dir / "epoch_metrics.json"
    metrics_path.write_text(json.dumps(metrics, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    ensure_tel(out_dir, args.emit_tel, args.emit_tel_events, series, args.mode, epoch_id)

    findings = analyze_epoch(out_dir)
    findings_path = out_dir / "epoch_findings.json"
    findings_path.write_text(json.dumps(findings, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    outputs_manifest = {
        "epoch_metrics.json": file_manifest(metrics_path),
        "epoch_findings.json": file_manifest(findings_path),
    }
    for optional in ("tel.json", "tel_events.jsonl", "telemetry.json", "epistemic_graph.json", "sophia_audit.json", "sophia_plan.json"):
        p = out_dir / optional
        if p.exists():
            outputs_manifest[optional] = file_manifest(p)

    epoch = {
        "schema": "agency_epoch_v1",
        "epoch_id": epoch_id,
        "started_at_utc": started_at,
        "ended_at_utc": ended_at,
        "prompt_hash": prompt_hash,
        "run_mode": args.mode,
        "seed": args.seed,
        "inputs_manifest": {
            "prompt_source": source,
            "prompt_hash": prompt_hash,
            "seed": args.seed,
            "mode": args.mode,
        },
        "outputs_manifest": outputs_manifest,
    }
    (out_dir / "epoch.json").write_text(json.dumps(epoch, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return epoch


def main() -> int:
    ap = argparse.ArgumentParser()
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--prompt-file", default="")
    src.add_argument("--prompt-text", default="")
    ap.add_argument("--mode", choices=["deterministic", "stochastic"], required=True)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--out", required=True)
    ap.add_argument("--emit-tel", action="store_true")
    ap.add_argument("--emit-tel-events", action="store_true")
    args = ap.parse_args()
    run_epoch(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
