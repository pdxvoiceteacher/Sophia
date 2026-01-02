from __future__ import annotations

import argparse
import csv
from pathlib import Path
from collections import defaultdict

import matplotlib.pyplot as plt


def read_rows(path: Path):
    rows = []
    with path.open("r", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            # coerce key numeric fields we care about
            row["seed"] = int(row["seed"])
            row["warn_LambdaT"] = float(row["warn_LambdaT"])
            row["max_LambdaT"] = float(row["max_LambdaT"])
            row["mean_Ppump"] = float(row["mean_Ppump"])
            row["mean_Qch"] = float(row["mean_Qch"])
            rows.append(row)
    return rows


def mean(xs):
    return sum(xs) / max(len(xs), 1)


def main() -> int:
    ap = argparse.ArgumentParser(description="Plot sweep results for TCHES ODE baseline vs lambda.")
    ap.add_argument("--infile", required=True, help="Path to sweep_summary.csv")
    ap.add_argument("--outdir", required=True, help="Output directory for figures")
    args = ap.parse_args()

    infile = Path(args.infile)
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    rows = read_rows(infile)

    by_ctl = defaultdict(list)
    for r in rows:
        by_ctl[r["controller"]].append(r)

    controllers = ["baseline", "lambda"]
    present = [c for c in controllers if c in by_ctl]
    if not present:
        raise SystemExit("No controllers found in sweep file.")

    # --- Boxplot: warn_LambdaT ---
    data_warn = [ [x["warn_LambdaT"] for x in by_ctl[c]] for c in present ]
    plt.figure()
    plt.boxplot(data_warn, labels=present)
    plt.ylabel("warn_LambdaT timesteps (Lambda_T > 0.7)")
    plt.title("Sweep distribution: warn_LambdaT")
    plt.tight_layout()
    out1 = outdir / "box_warn_LambdaT.png"
    plt.savefig(out1, dpi=200)

    # --- Boxplot: max_LambdaT ---
    data_max = [ [x["max_LambdaT"] for x in by_ctl[c]] for c in present ]
    plt.figure()
    plt.boxplot(data_max, labels=present)
    plt.ylabel("max_LambdaT")
    plt.title("Sweep distribution: max_LambdaT")
    plt.tight_layout()
    out2 = outdir / "box_max_LambdaT.png"
    plt.savefig(out2, dpi=200)

    # --- Bar: mean warn_LambdaT ---
    means_warn = [mean([x["warn_LambdaT"] for x in by_ctl[c]]) for c in present]
    plt.figure()
    plt.bar(present, means_warn)
    plt.ylabel("mean warn_LambdaT timesteps")
    plt.title("Mean warn_LambdaT by controller")
    plt.tight_layout()
    out3 = outdir / "bar_mean_warn_LambdaT.png"
    plt.savefig(out3, dpi=200)

    # --- Bar: mean pump power ---
    means_p = [mean([x["mean_Ppump"] for x in by_ctl[c]]) for c in present]
    plt.figure()
    plt.bar(present, means_p)
    plt.ylabel("mean pump power (kW)")
    plt.title("Mean pump power by controller")
    plt.tight_layout()
    out4 = outdir / "bar_mean_pump_power.png"
    plt.savefig(out4, dpi=200)

    print("Wrote:")
    for p in [out1, out2, out3, out4]:
        print(f"- {p}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
