from __future__ import annotations

import json
from pathlib import Path

from tools.telemetry import echo_test_runner


def _write_fake_epoch(epoch_dir: Path, *, result: str = "stable", psi: float = 0.6) -> None:
    epoch_dir.mkdir(parents=True, exist_ok=True)
    telemetry = {
        "result": result,
        "metrics": {
            "E": 0.5,
            "T": 0.8,
            "Psi": psi,
            "DeltaS": 0.2,
            "Lambda": 0.3,
            "Es": 0.4,
        },
    }
    (epoch_dir / "telemetry.json").write_text(json.dumps(telemetry) + "\n", encoding="utf-8")
    (epoch_dir / "tel_events.jsonl").write_text('{"event":"ok"}\n', encoding="utf-8")


def test_echo_replay_reports_no_anomalies_for_deterministic_epochs(monkeypatch, tmp_path: Path, capsys) -> None:
    def _fake_run_single_epoch(*, repo_root: Path, prompt: str, epoch_dir: Path, seed: int | None, epoch_index: int) -> Path:
        _write_fake_epoch(epoch_dir)
        return epoch_dir / "telemetry.json"

    monkeypatch.setattr(echo_test_runner, "run_single_epoch", _fake_run_single_epoch)

    summary = echo_test_runner.run_echo_benchmark(
        prompt="Echo test prompt",
        epochs=3,
        output_dir=tmp_path / "echo_results",
        seed=7,
        repo_root=tmp_path,
    )

    for i in range(1, 4):
        assert (tmp_path / "echo_results" / f"epoch_{i}" / "telemetry.json").exists()
    assert summary["anomalies"] == []
    captured = capsys.readouterr()
    assert "0 anomalies" in captured.out


def test_echo_replay_reports_anomalies_for_perturbed_epoch(monkeypatch, tmp_path: Path, capsys) -> None:
    def _fake_run_single_epoch(*, repo_root: Path, prompt: str, epoch_dir: Path, seed: int | None, epoch_index: int) -> Path:
        if epoch_index == 2:
            _write_fake_epoch(epoch_dir, result="drifted", psi=0.25)
        else:
            _write_fake_epoch(epoch_dir)
        return epoch_dir / "telemetry.json"

    monkeypatch.setattr(echo_test_runner, "run_single_epoch", _fake_run_single_epoch)

    summary = echo_test_runner.run_echo_benchmark(
        prompt="Echo test prompt",
        epochs=3,
        output_dir=tmp_path / "echo_results_bad",
        seed=None,
        repo_root=tmp_path,
    )

    assert len(summary["anomalies"]) >= 1
    assert any(item["epoch"] == 2 for item in summary["anomalies"])
    captured = capsys.readouterr()
    assert "anomalies" in captured.out
    assert "epoch_2" in captured.out
