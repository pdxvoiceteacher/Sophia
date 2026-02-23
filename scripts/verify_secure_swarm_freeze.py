#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator


def run(cmd: list[str], cwd: Path) -> None:
    subprocess.run(cmd, cwd=str(cwd), check=True)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def main() -> int:
    ap = argparse.ArgumentParser(description="Verify Secure Swarm Path A freeze contract invariants.")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--out-root", default="out/freeze_verify")
    ap.add_argument("--created-at-utc", default="2026-01-01T00:00:00Z")
    ap.add_argument("--bundle-id", default="bundle-freeze-contract")
    ap.add_argument("--simulate-peers", type=int, default=2)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--scenario", default="epoch_scenarios/baseline_deterministic.json")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    out_root = (repo / args.out_root).resolve()
    run_a = out_root / "run_a"
    run_b = out_root / "run_b"
    run_a.mkdir(parents=True, exist_ok=True)
    run_b.mkdir(parents=True, exist_ok=True)

    base_cmd = [
        sys.executable,
        "tools/telemetry/run_epoch_real.py",
        "--scenario",
        args.scenario,
        "--mode",
        "deterministic",
        "--seed",
        str(args.seed),
        "--simulate-peers",
        str(args.simulate_peers),
        "--created-at-utc",
        args.created_at_utc,
        "--bundle-id",
        args.bundle_id,
        "--quick",
        "--perturbations",
        "1",
    ]

    run([*base_cmd, "--out", str(run_a)], cwd=repo)
    run([*base_cmd, "--out", str(run_b)], cwd=repo)

    pa = run_a / "peer_attestations.json"
    pb = run_b / "peer_attestations.json"
    if not pa.exists() or not pb.exists():
        raise SystemExit("missing peer_attestations.json in one or both runs")
    if pa.read_bytes() != pb.read_bytes():
        raise SystemExit("peer_attestations.json differs across deterministic runs")

    consensus_schema = load_json(repo / "schema" / "consensus_summary_v1.schema.json")
    consensus = load_json(run_a / "consensus_summary.json")
    Draft202012Validator(consensus_schema).validate(consensus)

    print("[freeze_verify] OK deterministic peer_attestations and consensus schema validation")
    print(f"[freeze_verify] run_a={run_a}")
    print(f"[freeze_verify] run_b={run_b}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
