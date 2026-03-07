#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

_REPO_ROOT = Path(__file__).resolve().parents[2]
if __name__ == "__main__" and __package__ is None:
    _repo_root_s = str(_REPO_ROOT)
    if _repo_root_s not in sys.path:
        sys.path.insert(0, _repo_root_s)

_METRIC_KEYS: tuple[str, ...] = ("E", "T", "Psi", "DeltaS", "Lambda", "Es")


@dataclass(slots=True)
class EpochRun:
    epoch_index: int
    epoch_dir: Path
    telemetry_path: Path | None
    tel_paths: list[str]
    metrics: dict[str, float]
    result_signature: Any
    status: str
    error: str | None = None


def _extract_metrics(telemetry: dict[str, Any]) -> dict[str, float]:
    src = telemetry.get("metrics") if isinstance(telemetry, dict) else {}
    src = src if isinstance(src, dict) else {}
    out: dict[str, float] = {}
    key_candidates: dict[str, tuple[str, ...]] = {
        "E": ("E",),
        "T": ("T",),
        "Psi": ("Psi", "Ψ"),
        "DeltaS": ("DeltaS", "ΔS"),
        "Lambda": ("Lambda", "Λ"),
        "Es": ("Es", "Eₛ"),
    }
    for key, candidates in key_candidates.items():
        for candidate in candidates:
            value = src.get(candidate)
            if isinstance(value, (int, float)):
                out[key] = float(value)
                break
    return out


def _extract_result_signature(telemetry: dict[str, Any]) -> Any:
    if not isinstance(telemetry, dict):
        return None
    for key in ("result", "final_output", "summary", "decision"):
        if key in telemetry:
            return telemetry[key]
    return None


def _collect_tel_paths(epoch_dir: Path) -> list[str]:
    paths: list[str] = []
    for p in epoch_dir.glob("*.json*"):
        name = p.name.lower()
        if "tel" in name or "epistemic" in name:
            paths.append(p.name)
    return sorted(paths)


def run_single_epoch(*, repo_root: Path, prompt: str, epoch_dir: Path, seed: int | None, epoch_index: int) -> Path:
    epoch_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        sys.executable,
        "-m",
        "tools.telemetry.run_wrapper",
        "--out",
        str(epoch_dir),
        "--quick",
        "--perturbations",
        "1",
    ]
    env = dict(os.environ)
    env["ECHO_BENCH_PROMPT"] = prompt
    if seed is not None:
        env["ECHO_BENCH_SEED"] = str(seed + (epoch_index - 1))
    subprocess.run(cmd, cwd=str(repo_root), check=True, capture_output=True, text=True, env=env)
    telemetry_path = epoch_dir / "telemetry.json"
    if not telemetry_path.exists():
        raise FileNotFoundError(f"Expected telemetry output at {telemetry_path}")
    return telemetry_path


def _metrics_equal(a: Optional[float], b: Optional[float], abs_tol: float, rel_tol: float) -> bool:
    if a is None or b is None:
        return a is None and b is None
    diff = abs(a - b)
    if diff == 0:
        return True
    max_mag = max(abs(a), abs(b))
    return diff <= max(abs_tol, rel_tol * max_mag)


def _compare_epochs(runs: list[EpochRun], abs_tol: float = 1e-6, rel_tol: float = 1e-4) -> list[dict[str, Any]]:
    if not runs:
        return []
    baseline = runs[0]
    anomalies: list[dict[str, Any]] = []

    for run in runs[1:]:
        reasons: list[str] = []
        diverged_metrics: list[str] = []
        metric_deltas: dict[str, dict[str, float | None]] = {}

        if run.status != "success":
            reasons.append("status")

        if run.result_signature != baseline.result_signature:
            reasons.append("result_signature")

        all_metric_keys = set(_METRIC_KEYS) | set(baseline.metrics) | set(run.metrics)
        for key in sorted(all_metric_keys):
            a = baseline.metrics.get(key)
            b = run.metrics.get(key)
            if not _metrics_equal(a, b, abs_tol, rel_tol):
                reasons.append(f"metrics.{key}")
                diverged_metrics.append(key)
                metric_deltas[key] = {
                    "baseline": a,
                    "epoch": b,
                    "abs_diff": (abs(a - b) if a is not None and b is not None else None),
                }

        if run.tel_paths != baseline.tel_paths:
            reasons.append("tel_paths")

        if reasons:
            anomalies.append(
                {
                    "epoch": run.epoch_index,
                    "fields": reasons,
                    "diverged_metrics": sorted(set(diverged_metrics)),
                    "metric_deltas": metric_deltas,
                }
            )
    return anomalies


def run_echo_benchmark(
    *,
    prompt: str,
    epochs: int,
    output_dir: Path,
    seed: int | None,
    abs_tol: float = 1e-6,
    rel_tol: float = 1e-4,
    repo_root: Path | None = None,
) -> dict[str, Any]:
    repo = (repo_root or _REPO_ROOT).resolve()
    output_dir = output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    runs: list[EpochRun] = []
    for epoch_index in range(1, epochs + 1):
        epoch_dir = output_dir / f"epoch_{epoch_index}"
        epoch_dir.mkdir(parents=True, exist_ok=True)
        telemetry_path: Path | None = None
        metrics: dict[str, float] = {}
        result_signature: Any = None
        status = "success"
        error: str | None = None

        try:
            telemetry_path = run_single_epoch(repo_root=repo, prompt=prompt, epoch_dir=epoch_dir, seed=seed, epoch_index=epoch_index)
            telemetry_payload = json.loads(telemetry_path.read_text(encoding="utf-8-sig"))
            metrics = _extract_metrics(telemetry_payload)
            result_signature = _extract_result_signature(telemetry_payload)
        except Exception as exc:  # noqa: BLE001
            status = "failed"
            error = repr(exc)

        metrics_path = epoch_dir / "metrics.json"
        metrics_path.write_text(
            json.dumps({"epoch_index": epoch_index, "metrics": metrics}, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

        runs.append(
            EpochRun(
                epoch_index=epoch_index,
                epoch_dir=epoch_dir,
                telemetry_path=telemetry_path,
                tel_paths=_collect_tel_paths(epoch_dir),
                metrics=metrics,
                result_signature=result_signature,
                status=status,
                error=error,
            )
        )

    anomalies = _compare_epochs(runs, abs_tol=abs_tol, rel_tol=rel_tol)
    anomaly_by_epoch = {item["epoch"]: item for item in anomalies}

    per_epoch: list[dict[str, Any]] = []
    diverged_metrics_overall: set[str] = set()
    for run in runs:
        anomaly_entry = anomaly_by_epoch.get(run.epoch_index)
        is_anomaly = run.status != "success" or anomaly_entry is not None
        diverged_metrics = list(anomaly_entry.get("diverged_metrics", [])) if anomaly_entry else []
        diverged_metrics_overall.update(diverged_metrics)
        entry = {
            "epoch_index": run.epoch_index,
            "metrics": run.metrics,
            "status": run.status,
            "anomaly": is_anomaly,
            "diverged_metrics": diverged_metrics,
            "telemetry_path": str(run.telemetry_path) if run.telemetry_path else None,
            "tel_paths": run.tel_paths,
        }
        if anomaly_entry:
            entry["anomaly_details"] = {
                "fields": anomaly_entry.get("fields", []),
                "metric_deltas": anomaly_entry.get("metric_deltas", {}),
            }
        if run.error:
            entry["error"] = run.error
        per_epoch.append(entry)

    num_anomalous = sum(1 for item in per_epoch if item["anomaly"])
    deterministic = epochs - num_anomalous

    summary = {
        "prompt": prompt,
        "epochs": epochs,
        "abs_tol": abs_tol,
        "rel_tol": rel_tol,
        "created_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "per_epoch": per_epoch,
        "summary": {
            "num_epochs": epochs,
            "num_anomalous_epochs": num_anomalous,
            "diverged_metrics_overall": sorted(diverged_metrics_overall),
        },
        # Backward-compatible fields for existing tests/tooling:
        "deterministic": deterministic,
        "anomalies": anomalies,
    }
    (output_dir / "echo_summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(f'Echo benchmark for prompt "{prompt}" : {epochs} epochs, {deterministic} deterministic, {num_anomalous} anomalies')
    for item in per_epoch:
        if item["anomaly"]:
            fields = item.get("anomaly_details", {}).get("fields", [])
            if item.get("error"):
                print(f"- epoch_{item['epoch_index']} diverged: status,error")
            else:
                print(f"- epoch_{item['epoch_index']} diverged: {', '.join(fields)}")

    return summary


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Run Echo replay benchmark across multiple epochs")
    p.add_argument("-p", "--prompt", required=True, help="Prompt to replay across epochs")
    p.add_argument("-e", "--epochs", type=int, default=3, help="Number of replay epochs (default: 3)")
    p.add_argument("-o", "--output-dir", default="./echo_results", help="Directory to write benchmark outputs")
    p.add_argument("--seed", type=int, default=None, help="Optional seed for repeatability")
    p.add_argument(
        "--abs-tol",
        type=float,
        default=1e-6,
        help="Absolute tolerance for numeric metric comparison (default: 1e-6)",
    )
    p.add_argument(
        "--rel-tol",
        type=float,
        default=1e-4,
        help="Relative tolerance for numeric metric comparison (default: 1e-4)",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    run_echo_benchmark(
        prompt=args.prompt,
        epochs=int(args.epochs),
        output_dir=Path(args.output_dir),
        seed=args.seed,
        abs_tol=float(args.abs_tol),
        rel_tol=float(args.rel_tol),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
