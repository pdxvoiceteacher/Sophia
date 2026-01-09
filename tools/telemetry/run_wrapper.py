#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, platform, subprocess, sys, statistics
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)

def load_json_bom_safe(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    except Exception:
        return "unknown"

def run_ucc(module: str, input_path: Path, outdir: Path) -> tuple[Path, Path]:
    """
    Run a UCC module and return (audit_bundle.json, telemetry_snapshot.json) paths.
    Assumes telemetry_snapshot_v1.yml is available and emit_telemetry_snapshot is registered.
    """
    outdir.mkdir(parents=True, exist_ok=True)

    # 1) Run module
    run([sys.executable, "-m", "ucc.cli", "run", module, "--input", str(input_path), "--outdir", str(outdir)], cwd=REPO)
    audit_bundle = outdir / "audit_bundle.json"
    if not audit_bundle.exists():
        raise SystemExit(f"Missing audit_bundle.json at {audit_bundle}")

    # 2) Run canonical telemetry snapshot (input = audit_bundle)
    snap_out = outdir / "telemetry_snapshot_out"
    snap_out.mkdir(parents=True, exist_ok=True)

    run([sys.executable, "-m", "ucc.cli", "run", "ucc/modules/telemetry_snapshot_v1.yml",
         "--input", str(audit_bundle), "--outdir", str(snap_out)], cwd=REPO)

    snap_json = snap_out / "telemetry_snapshot.json"
    if not snap_json.exists():
        raise SystemExit(f"Missing telemetry_snapshot.json at {snap_json}")

    return audit_bundle, snap_json

def metric_vec(telemetry_snapshot_json: Path) -> dict[str, float]:
    d = load_json_bom_safe(telemetry_snapshot_json)
    m = d.get("metrics", {}) or {}
    return {
        "E": float(m.get("E", 1.0)),
        "T": float(m.get("T", 1.0)),
        "Psi": float(m.get("Psi", 1.0)),
        "Es": float(m.get("Es", 1.0)),
    }

def drift(a: dict[str, float], b: dict[str, float]) -> float:
    # Mean absolute drift across core coherence metrics (bounded 0..1 typically)
    keys = ["E", "T", "Psi", "Es"]
    return sum(abs(a[k] - b[k]) for k in keys) / len(keys)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="Output directory for telemetry run")
    ap.add_argument("--quick", action="store_true", help="Quick mode (smoke)")
    ap.add_argument("--perturbations", type=int, default=3, help="Number of repeat perturbation runs for ΔS/Λ")
    args = ap.parse_args()

    outdir = Path(args.out).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    # 0) Run KONOMI smoke
    smoke_out = outdir / "konomi_smoke_out"
    smoke_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable,
        "python/experiments/konomi_smoke/run_smoke.py",
        "--quick" if args.quick else "--full",
        "--outdir", str(smoke_out)
    ], cwd=REPO)

    summary = smoke_out / "konomi_smoke_summary.json"
    if not summary.exists():
        raise SystemExit(f"Missing expected smoke summary: {summary}")

    # 1) Base coverage run
    cov_out = outdir / "ucc_cov_out"
    audit_bundle, snap_json = run_ucc("ucc/modules/konomi_smoke_coverage.yml", summary, cov_out)

    base_vec = metric_vec(snap_json)

    # 2) Perturbation runs: re-run the same module N times to measure repeatability drift
    pert_results = []
    distances = []

    for i in range(1, max(0, args.perturbations) + 1):
        pdir = outdir / f"ucc_cov_perturb_{i}"
        ab_i, snap_i = run_ucc("ucc/modules/konomi_smoke_coverage.yml", summary, pdir)
        vec_i = metric_vec(snap_i)

        d_i = drift(base_vec, vec_i)
        distances.append(d_i)

        pert_results.append({
            "i": i,
            "audit_bundle_path": str(ab_i.relative_to(REPO)).replace("\\", "/"),
            "telemetry_snapshot_path": str(snap_i.relative_to(REPO)).replace("\\", "/"),
            "metrics": vec_i,
            "drift_from_base": d_i
        })

    # 3) Compute ΔS/Λ
    # ΔS = mean drift (repeatability entropy)
    # Λ = max drift (volatility / worst-case)
    if distances:
        deltaS = float(statistics.mean(distances))
        lam = float(max(distances))
    else:
        deltaS = 0.0
        lam = 0.0

    # 4) Write perturbations report (artifact)
    pert_path = outdir / "perturbations.json"
    pert_doc = {
        "kind": "telemetry_perturbations.v1",
        "base": {
            "audit_bundle_path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"),
            "telemetry_snapshot_path": str(snap_json.relative_to(REPO)).replace("\\", "/"),
            "metrics": base_vec
        },
        "perturbations": pert_results,
        "deltaS": deltaS,
        "lambda": lam
    }
    pert_path.write_text(json.dumps(pert_doc, indent=2, sort_keys=True), encoding="utf-8")

    # 5) Build final telemetry.json (canonical metrics + computed ΔS/Λ)
    snap = load_json_bom_safe(snap_json)
    snap_metrics = snap.get("metrics", {}) or {}
    snap_flags = snap.get("flags", {}) or {}

    metrics = dict(snap_metrics)
    metrics["DeltaS"] = deltaS
    metrics["Lambda"] = lam

    artifacts = [
        {"path": str(summary.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(summary)},
        {"path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(audit_bundle)},
        {"path": str(snap_json.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(snap_json)},
        {"path": str(pert_path.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(pert_path)},
    ]

    telemetry = {
        "schema_id": snap.get("schema_id", "coherencelattice.telemetry_run.v1"),
        "version": int(snap.get("version", 1)),
        "run_id": outdir.name,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "python": sys.version.replace("\\n", " "),
            "platform": platform.platform(),
            "git_commit": git_commit()
        },
        "metrics": metrics,
        "flags": dict(snap_flags, **{
            "telemetry_ok": bool(snap_flags.get("telemetry_ok", True)),
            "perturbations_count": len(distances),
            "deltaS_from_perturbations": deltaS,
            "lambda_from_perturbations": lam
        }),
        "artifacts": artifacts,
        "ucc": {
            "audit_bundle_path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"),
            "audit_bundle_sha256": sha256_file(audit_bundle)
        },
        "notes": f"ΔS/Λ computed from {len(distances)} repeat perturbation runs (repeatability drift)."
    }

    out_json = outdir / "telemetry.json"
    out_json.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[run_wrapper] wrote {out_json}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
