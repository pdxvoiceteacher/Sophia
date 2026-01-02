from __future__ import annotations

import argparse
import csv
from pathlib import Path
import numpy as np


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--infile", required=True)
    ap.add_argument("--out_md", default=None)
    args = ap.parse_args()

    p = Path(args.infile)
    rows = []
    with p.open("r", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            rows.append(row)

    def colf(name):
        return np.array([float(x[name]) for x in rows], dtype=np.float64)

    lam = colf("Lambda_T")
    E = colf("E_model")
    T = colf("T_transparency")
    PsiTE = colf("Psi_TE")
    Es = colf("Es_site")
    Ppump = colf("P_pump_kW")
    Qch = colf("Q_chiller_kW")

    warnL = colf("warn_LambdaT").sum()
    alarmL = colf("alarm_LambdaT").sum()

    warnE = colf("warn_E").sum()
    alarmE = colf("alarm_E").sum()

    warnT = colf("warn_T").sum()
    alarmT = colf("alarm_T").sum()

    warnPsi = colf("warn_Psi").sum()
    alarmEs = colf("alarm_Es").sum()

    md = []
    md.append(f"# TCHES ODE Summary: `{p.as_posix()}`\n")
    md.append(f"- max(ΛT) = **{lam.max():.3g}**, mean(ΛT) = {lam.mean():.3g}")
    md.append(f"- min(E) = **{E.min():.3g}**, min(T) = **{T.min():.3g}**, min(Psi_TE) = **{PsiTE.min():.3g}**, min(Es) = **{Es.min():.3g}**")
    md.append(f"- pump energy proxy: mean(P_pump) = {Ppump.mean():.3g} kW")
    md.append(f"- chiller load proxy: mean(Q_chiller) = {Qch.mean():.3g} kW\n")
    md.append("## Threshold events (counts of timesteps)\n")
    md.append(f"- ΛT warn>0.7: {int(warnL)} ; alarm>1.0: {int(alarmL)}")
    md.append(f"- E warn<0.8: {int(warnE)} ; alarm<0.6: {int(alarmE)}")
    md.append(f"- T warn<0.85: {int(warnT)} ; alarm<0.7: {int(alarmT)}")
    md.append(f"- Ψ_TE warn<0.7: {int(warnPsi)}")
    md.append(f"- Es alarm<0.8: {int(alarmEs)}")

    out_md = Path(args.out_md) if args.out_md else p.with_suffix(".summary.md")
    out_md.write_text("\n".join(md), encoding="utf-8")
    print(f"Wrote: {out_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
