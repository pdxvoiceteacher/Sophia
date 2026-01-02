from __future__ import annotations

import argparse
import csv
from pathlib import Path
import numpy as np
import importlib.util
import sys


def summarize_csv(path: Path) -> dict:
    rows = []
    with path.open("r", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            rows.append(row)

    def farr(name: str) -> np.ndarray:
        return np.array([float(x[name]) for x in rows], dtype=np.float64)

    lam = farr("Lambda_T")
    E = farr("E_model")
    T = farr("T_transparency")
    PsiTE = farr("Psi_TE")
    Es = farr("Es_site")
    Ppump = farr("P_pump_kW")
    Qch = farr("Q_chiller_kW")

    warnL = int((lam > 0.7).sum())
    alarmL = int((lam > 1.0).sum())
    warnE = int((E < 0.8).sum())
    alarmE = int((E < 0.6).sum())
    warnT = int((T < 0.85).sum())
    alarmT = int((T < 0.7).sum())
    warnPsi = int((PsiTE < 0.7).sum())
    alarmEs = int((Es < 0.8).sum())

    return dict(
        max_LambdaT=float(lam.max()),
        mean_LambdaT=float(lam.mean()),
        warn_LambdaT=warnL,
        alarm_LambdaT=alarmL,
        min_E=float(E.min()),
        warn_E=warnE,
        alarm_E=alarmE,
        min_T=float(T.min()),
        warn_T=warnT,
        alarm_T=alarmT,
        min_PsiTE=float(PsiTE.min()),
        warn_PsiTE=warnPsi,
        min_Es=float(Es.min()),
        alarm_Es=alarmEs,
        mean_Ppump=float(Ppump.mean()),
        mean_Qch=float(Qch.mean()),
    )


def mean_std(xs: np.ndarray):
    if xs.size == 0:
        return (np.nan, np.nan)
    if xs.size == 1:
        return (float(xs[0]), 0.0)
    return (float(xs.mean()), float(xs.std(ddof=1)))


def fmt(m, s):
    return f"{m:.4g} ± {s:.3g}"


def load_run_function() -> callable:
    """
    Dynamically import run.py in a way compatible with Python 3.14 dataclasses:
    register module in sys.modules before exec_module.
    """
    here = Path(__file__).resolve().parent
    run_path = here / "run.py"

    spec = importlib.util.spec_from_file_location("tches_run_module", run_path)
    assert spec and spec.loader

    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod  # <-- critical for dataclasses in Py 3.14+
    spec.loader.exec_module(mod)

    return mod.run


def main() -> int:
    ap = argparse.ArgumentParser(description="Run 20-seed sweep for TCHES ODE baseline vs lambda.")
    ap.add_argument("--seeds", type=int, default=20)
    ap.add_argument("--outdir", type=str, default="python/experiments/tches_ode/out/sweep")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    run = load_run_function()

    rows_out = []
    for seed in range(args.seeds):
        for controller in ["baseline", "lambda"]:
            out_csv = outdir / f"{controller}_seed{seed}.csv"
            run(controller, out_csv, seed, duration_s=2400, dt_s=1.0)
            stats = summarize_csv(out_csv)
            rows_out.append(dict(seed=seed, controller=controller, **stats))

    summary_csv = outdir / "sweep_summary.csv"
    keys = ["seed", "controller"] + [k for k in rows_out[0].keys() if k not in ("seed", "controller")]
    with summary_csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        for r in rows_out:
            w.writerow(r)

    agg_md = outdir / "sweep_aggregate.md"
    with agg_md.open("w", encoding="utf-8") as f:
        f.write("# TCHES ODE 20-seed sweep (baseline vs lambda)\n\n")
        f.write(f"Seeds: 0..{args.seeds-1}\n\n")

        for controller in ["baseline", "lambda"]:
            sel = [r for r in rows_out if r["controller"] == controller]
            f.write(f"## {controller}\n\n")

            for metric in [
                "max_LambdaT", "mean_LambdaT", "warn_LambdaT", "alarm_LambdaT",
                "min_E", "warn_E", "alarm_E",
                "min_T", "alarm_T",
                "min_PsiTE", "warn_PsiTE",
                "min_Es", "alarm_Es",
                "mean_Ppump", "mean_Qch",
            ]:
                arr = np.array([float(r[metric]) for r in sel], dtype=np.float64)
                m, s = mean_std(arr)
                f.write(f"- {metric}: {fmt(m, s)}\n")
            f.write("\n")

    print(f"Wrote:\n- {summary_csv}\n- {agg_md}\n(Per-seed CSVs are in {outdir})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
