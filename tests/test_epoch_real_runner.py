from __future__ import annotations

import hashlib
import json
from pathlib import Path

from tools.telemetry import run_epoch_real


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_epoch_scenarios_exist() -> None:
    root = Path(__file__).resolve().parents[1]
    scenarios = sorted((root / "epoch_scenarios").glob("*.json"))
    assert len(scenarios) >= 3


def test_deterministic_tel_hash_replay(monkeypatch, tmp_path: Path) -> None:
    def fake_run_pipeline(out_dir: Path, quick: bool, perturbations: int, emit_tel: bool, emit_tel_events: bool) -> None:
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "tel.json").write_text(
            json.dumps(
                {
                    "run_id": out_dir.name,
                    "created_at": "2026-01-01T00:00:00Z",
                    "environment": {"git_commit": "abc123"},
                    "graph": {
                        "nodes": [{"id": "n1", "kind": "branch", "depth": 1}],
                        "edges": [],
                    },
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        (out_dir / "telemetry.json").write_text(
            json.dumps(
                {"metrics": {"E": 0.7, "T": 0.8, "Psi": 0.56, "DeltaS": 0.1, "Lambda": 0.2, "Es": 0.9}},
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        if emit_tel_events:
            (out_dir / "tel_events.jsonl").write_text('{"event":"epoch_step","step":0}\n', encoding="utf-8")

    monkeypatch.setattr(run_epoch_real, "run_pipeline", fake_run_pipeline)

    args1 = type("Args", (), {
        "scenario": "epoch_scenarios/baseline_deterministic.json",
        "prompt_text": "",
        "mode": "deterministic",
        "seed": 7,
        "out": str(tmp_path / "a"),
        "baseline_run_dir": "",
        "emit_tel": True,
        "emit_tel_events": True,
    })
    args2 = type("Args", (), {
        "scenario": "epoch_scenarios/baseline_deterministic.json",
        "prompt_text": "",
        "mode": "deterministic",
        "seed": 7,
        "out": str(tmp_path / "b"),
        "baseline_run_dir": "",
        "emit_tel": True,
        "emit_tel_events": True,
    })

    run_epoch_real.run_epoch_real(args1)
    run_epoch_real.run_epoch_real(args2)

    assert sha(tmp_path / "a" / "tel.json") == sha(tmp_path / "b" / "tel.json")
    assert (tmp_path / "a" / "retrospection.json").exists()
    assert (tmp_path / "a" / "sentinel_state.json").exists()


def test_epoch_outputs_manifest_includes_attestations_when_present(monkeypatch, tmp_path: Path) -> None:
    def fake_run_pipeline(out_dir: Path, quick: bool, perturbations: int, emit_tel: bool, emit_tel_events: bool) -> None:
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "tel.json").write_text('{"run_id":"x","created_at":"2026-01-01T00:00:00Z","environment":{"git_commit":"abc"}}\n', encoding="utf-8")
        (out_dir / "telemetry.json").write_text('{"metrics":{"E":0.1,"T":0.2,"Psi":0.02,"DeltaS":0.0,"Lambda":0.0,"Es":0.1}}\n', encoding="utf-8")
        (out_dir / "attestations.json").write_text('{"schema":"attestations_v1","status":"pending"}\n', encoding="utf-8")

    monkeypatch.setattr(run_epoch_real, "run_pipeline", fake_run_pipeline)
    args = type("Args", (), {
        "scenario": "epoch_scenarios/baseline_deterministic.json",
        "prompt_text": "",
        "mode": "deterministic",
        "seed": 7,
        "out": str(tmp_path / "run"),
        "baseline_run_dir": "",
        "emit_tel": True,
        "emit_tel_events": False,
    })
    run_epoch_real.run_epoch_real(args)
    epoch = json.loads((tmp_path / "run" / "epoch.json").read_text(encoding="utf-8"))
    assert "attestations.json" in (epoch.get("outputs_manifest") or {})


def test_run_epoch_real_passes_quick_and_perturbations_overrides(monkeypatch, tmp_path: Path) -> None:
    captured = {}

    def fake_run_pipeline(out_dir: Path, quick: bool, perturbations: int, emit_tel: bool, emit_tel_events: bool) -> None:
        captured["quick"] = quick
        captured["perturbations"] = perturbations
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "tel.json").write_text('{\"run_id\":\"x\",\"created_at\":\"2026-01-01T00:00:00Z\",\"environment\":{\"git_commit\":\"abc\"}}\n', encoding="utf-8")
        (out_dir / "telemetry.json").write_text('{\"metrics\":{\"E\":0.1,\"T\":0.2,\"Psi\":0.02,\"DeltaS\":0.0,\"Lambda\":0.0,\"Es\":0.1}}\n', encoding="utf-8")

    monkeypatch.setattr(run_epoch_real, "run_pipeline", fake_run_pipeline)

    args = type("Args", (), {
        "scenario": "epoch_scenarios/baseline_deterministic.json",
        "prompt_text": "",
        "mode": "deterministic",
        "seed": 7,
        "out": str(tmp_path / "run"),
        "baseline_run_dir": "",
        "emit_tel": False,
        "emit_tel_events": False,
        "quick": True,
        "perturbations": 9,
    })
    run_epoch_real.run_epoch_real(args)

    assert captured["quick"] is True
    assert captured["perturbations"] == 9
