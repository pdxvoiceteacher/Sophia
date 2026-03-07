#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

_METRICS = ("E", "T", "Psi", "DeltaS", "Lambda", "Es")


def discover_summaries(root: Path, recursive: bool) -> list[Path]:
    pattern = "**/echo_summary.json" if recursive else "*/echo_summary.json"
    return sorted(root.glob(pattern))


def _mean_std(values: list[float]) -> dict[str, float]:
    if not values:
        return {"mean": 0.0, "std": 0.0}
    mean = sum(values) / len(values)
    var = sum((v - mean) ** 2 for v in values) / len(values)
    return {"mean": mean, "std": math.sqrt(var)}


def aggregate_echo_summaries(summary_paths: list[Path]) -> dict[str, Any]:
    total_epochs = 0
    anomalous_epochs = 0
    per_metric_counts = {k: 0 for k in _METRICS}
    metric_values = {k: [] for k in _METRICS}
    per_prompt: dict[str, dict[str, int]] = {}

    for path in summary_paths:
        data = json.loads(path.read_text(encoding="utf-8-sig"))
        prompt = str(data.get("prompt", "unknown"))
        per_epoch = data.get("per_epoch") or []
        if not isinstance(per_epoch, list):
            per_epoch = []

        per_prompt.setdefault(prompt, {"epochs": 0, "anomalous_epochs": 0})

        for epoch in per_epoch:
            if not isinstance(epoch, dict):
                continue
            total_epochs += 1
            per_prompt[prompt]["epochs"] += 1

            metrics = epoch.get("metrics")
            if isinstance(metrics, dict):
                for key in _METRICS:
                    val = metrics.get(key)
                    if isinstance(val, (int, float)):
                        metric_values[key].append(float(val))

            is_anomaly = bool(epoch.get("anomaly"))
            if is_anomaly:
                anomalous_epochs += 1
                per_prompt[prompt]["anomalous_epochs"] += 1
                for key in epoch.get("diverged_metrics") or []:
                    if key in per_metric_counts:
                        per_metric_counts[key] += 1

    per_metric_rates = {
        key: {
            "count": per_metric_counts[key],
            "rate": (per_metric_counts[key] / total_epochs) if total_epochs else 0.0,
            **_mean_std(metric_values[key]),
        }
        for key in _METRICS
    }

    return {
        "benchmarks": len(summary_paths),
        "total_epochs": total_epochs,
        "anomalous_epochs": anomalous_epochs,
        "overall_anomaly_rate": (anomalous_epochs / total_epochs) if total_epochs else 0.0,
        "per_metric": per_metric_rates,
        "per_prompt": per_prompt,
    }


def print_report(agg: dict[str, Any]) -> None:
    print("Echo Anomaly Report:")
    print(f"  Benchmarks: {agg['benchmarks']}")
    print(f"  Total epochs: {agg['total_epochs']}")
    print(f"  Anomalous epochs: {agg['anomalous_epochs']} ({agg['overall_anomaly_rate'] * 100:.1f}%)")
    print("  Per-metric anomaly rates:")
    for metric, stats in agg["per_metric"].items():
        print(f"    {metric}: {stats['count']} / {agg['total_epochs']}")
    print("  Per-prompt:")
    for prompt, stats in agg["per_prompt"].items():
        print(f"    \"{prompt}\": {stats['anomalous_epochs']} / {stats['epochs']} anomalous epochs")


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Aggregate echo_summary.json anomaly telemetry")
    p.add_argument("--dir", required=True, help="Directory containing echo results and echo_summary.json files")
    p.add_argument("--output", default=None, help="Optional path to write aggregated JSON")
    p.add_argument("--recursive", action="store_true", help="Recursively search for echo_summary.json files")
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    root = Path(args.dir).resolve()
    summaries = discover_summaries(root, recursive=bool(args.recursive))
    agg = aggregate_echo_summaries(summaries)
    print_report(agg)
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(agg, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
