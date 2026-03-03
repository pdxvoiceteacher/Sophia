#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_REPO_ROOT = Path(__file__).resolve().parents[2]
if __name__ == "__main__" and __package__ is None:
    _repo_root_s = str(_REPO_ROOT)
    if _repo_root_s not in sys.path:
        sys.path.insert(0, _repo_root_s)

_METRIC_KEYS: tuple[tuple[str, str], ...] = (
    ("E", "E"),
    ("T", "T"),
    ("Psi", "Ψ"),
    ("DeltaS", "ΔS"),
    ("Lambda", "Λ"),
    ("Es", "Eₛ"),
)


@dataclass(slots=True)
class EpochRun:
    epoch_index: int
    epoch_dir: Path
    telemetry_path: Path
    tel_paths: list[str]
    metrics: dict[str, float]
    result_signature: Any


def _extract_metrics(telemetry: dict[str, Any]) -> dict[str, float]:
    src = telemetry.get("metrics") if isinstance(telemetry, dict) else {}
    src = src if isinstance(src, dict) else {}
    out: dict[str, float] = {}
    for key, out_key in _METRIC_KEYS:
        value = src.get(key)
        if isinstance(value, (int, float)):
            out[out_key] = float(value)
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


def _compare_epochs(runs: list[EpochRun], tolerance: float = 1e-9) -> list[dict[str, Any]]:
    if not runs:
        return []
    baseline = runs[0]
    anomalies: list[dict[str, Any]] = []

    for run in runs[1:]:
        reasons: list[str] = []

        if run.result_signature != baseline.result_signature:
            reasons.append("result_signature")

        all_metric_keys = set(baseline.metrics) | set(run.metrics)
        for key in sorted(all_metric_keys):
            a = baseline.metrics.get(key)
            b = run.metrics.get(key)
            if a is None or b is None:
                if a != b:
                    reasons.append(f"metrics.{key}")
                continue
            if abs(a - b) > tolerance:
                reasons.append(f"metrics.{key}")

        if run.tel_paths != baseline.tel_paths:
            reasons.append("tel_paths")

        if reasons:
            anomalies.append({"epoch": run.epoch_index, "fields": reasons})
    return anomalies


def run_echo_benchmark(*, prompt: str, epochs: int, output_dir: Path, seed: int | None, repo_root: Path | None = None) -> dict[str, Any]:
    repo = (repo_root or _REPO_ROOT).resolve()
    output_dir = output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    runs: list[EpochRun] = []
    for epoch_index in range(1, epochs + 1):
        epoch_dir = output_dir / f"epoch_{epoch_index}"
        telemetry_path = run_single_epoch(repo_root=repo, prompt=prompt, epoch_dir=epoch_dir, seed=seed, epoch_index=epoch_index)

        telemetry_payload = json.loads(telemetry_path.read_text(encoding="utf-8-sig"))
        run = EpochRun(
            epoch_index=epoch_index,
            epoch_dir=epoch_dir,
            telemetry_path=telemetry_path,
            tel_paths=_collect_tel_paths(epoch_dir),
            metrics=_extract_metrics(telemetry_payload),
            result_signature=_extract_result_signature(telemetry_payload),
        )
        runs.append(run)

    anomalies = _compare_epochs(runs)
    deterministic = epochs - len(anomalies)

    summary = {
        "prompt": prompt,
        "epochs": epochs,
        "deterministic": deterministic,
        "anomalies": anomalies,
        "epochs_data": [
            {
                "epoch": run.epoch_index,
                "telemetry_path": str(run.telemetry_path),
                "tel_paths": run.tel_paths,
                "metrics": run.metrics,
            }
            for run in runs
        ],
    }
    (output_dir / "echo_summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(f'Echo benchmark for prompt "{prompt}" : {epochs} epochs, {deterministic} deterministic, {len(anomalies)} anomalies')
    for anomaly in anomalies:
        print(f"- epoch_{anomaly['epoch']} diverged: {', '.join(anomaly['fields'])}")

    return summary


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Run Echo replay benchmark across multiple epochs")
    p.add_argument("-p", "--prompt", required=True, help="Prompt to replay across epochs")
    p.add_argument("-e", "--epochs", type=int, default=3, help="Number of replay epochs (default: 3)")
    p.add_argument("-o", "--output-dir", default="./echo_results", help="Directory to write benchmark outputs")
    p.add_argument("--seed", type=int, default=None, help="Optional seed for repeatability")
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    run_echo_benchmark(prompt=args.prompt, epochs=int(args.epochs), output_dir=Path(args.output_dir), seed=args.seed)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
