from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib.pyplot as plt


def read_series(path: Path):
    t = []
    lam = []
    Tb = []
    with path.open("r", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            t.append(float(row["t_s"]))
            lam.append(float(row["Lambda_T"]))
            Tb.append(float(row["T_block_C"]))
    return t, lam, Tb


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--lambda", dest="lambda_path", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--title", default="Lambda_T comparison")
    args = ap.parse_args()

    p_base = Path(args.baseline)
    p_lam = Path(args.lambda_path)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    t0, lam0, Tb0 = read_series(p_base)
    t1, lam1, Tb1 = read_series(p_lam)

    plt.figure()
    plt.plot(t0, lam0, label="baseline")
    plt.plot(t1, lam1, label="lambda-aware")
    plt.axhline(0.7, linestyle="--", linewidth=1, label="warn (0.7)")
    plt.axhline(1.0, linestyle="--", linewidth=1, label="alarm (1.0)")
    plt.xlabel("time (s)")
    plt.ylabel("Lambda_T")
    plt.title(args.title)
    plt.legend()
    plt.tight_layout()
    plt.savefig(out, dpi=200)

    # Optional second plot: temperature
    out2 = out.with_name(out.stem + "_Tblock.png")
    plt.figure()
    plt.plot(t0, Tb0, label="baseline")
    plt.plot(t1, Tb1, label="lambda-aware")
    plt.axhline(45.0, linestyle="--", linewidth=1, label="T_set")
    plt.xlabel("time (s)")
    plt.ylabel("T_block (C)")
    plt.title("T_block comparison")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out2, dpi=200)

    print(f"Wrote:\n- {out}\n- {out2}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
