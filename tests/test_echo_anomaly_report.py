from __future__ import annotations

import json
from pathlib import Path

from tools.telemetry import echo_anomaly_report


def _write_summary(path: Path, prompt: str, per_epoch: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "prompt": prompt,
        "per_epoch": per_epoch,
    }
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def test_aggregate_echo_summaries_counts_epochs_anomalies_and_metrics(tmp_path: Path) -> None:
    _write_summary(
        tmp_path / "run_a" / "echo_summary.json",
        "Prompt A",
        [
            {"epoch_index": 1, "anomaly": False, "diverged_metrics": [], "metrics": {"E": 0.5, "Psi": 0.7}},
            {"epoch_index": 2, "anomaly": True, "diverged_metrics": ["E", "DeltaS"], "metrics": {"E": 0.6, "DeltaS": 0.2}},
        ],
    )
    _write_summary(
        tmp_path / "run_b" / "echo_summary.json",
        "Prompt B",
        [
            {"epoch_index": 1, "anomaly": True, "diverged_metrics": ["Psi"], "metrics": {"Psi": 0.9, "Lambda": 0.3}},
            {"epoch_index": 2, "anomaly": False, "diverged_metrics": [], "metrics": {"Psi": 0.9, "Lambda": 0.3}},
            {"epoch_index": 3, "anomaly": True, "diverged_metrics": ["E", "Lambda"], "metrics": {"E": 0.4, "Lambda": 0.1}},
        ],
    )

    summaries = echo_anomaly_report.discover_summaries(tmp_path, recursive=True)
    agg = echo_anomaly_report.aggregate_echo_summaries(summaries)

    assert agg["benchmarks"] == 2
    assert agg["total_epochs"] == 5
    assert agg["anomalous_epochs"] == 3
    assert agg["per_metric"]["E"]["count"] == 2
    assert agg["per_metric"]["Psi"]["count"] == 1
    assert agg["per_metric"]["DeltaS"]["count"] == 1
    assert agg["per_metric"]["Lambda"]["count"] == 1
    assert agg["per_prompt"]["Prompt A"]["anomalous_epochs"] == 1
    assert agg["per_prompt"]["Prompt B"]["anomalous_epochs"] == 2


def test_report_main_writes_output_json(tmp_path: Path) -> None:
    _write_summary(
        tmp_path / "run" / "echo_summary.json",
        "Prompt",
        [{"epoch_index": 1, "anomaly": False, "diverged_metrics": [], "metrics": {"E": 0.1}}],
    )
    out = tmp_path / "report.json"
    rc = echo_anomaly_report.main(["--dir", str(tmp_path), "--recursive", "--output", str(out)])
    assert rc == 0
    assert out.exists()
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["benchmarks"] == 1
