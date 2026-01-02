from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np


def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def clamp01(x: float) -> float:
    return clamp(x, 0.0, 1.0)


@dataclass
class Params:
    # --- Thermal block (reduced-order) ---
    C_block_kJ_per_C: float = 5000.0   # thermal capacitance of block (kJ/°C)
    k_cool_kW_per_C: float = 35.0     # max heat-removal coefficient at u_pump=1 (kW/°C)
    T_env_C: float = 20.0              # baseline "inlet/ambient" temp (°C)
    T_set_C: float = 45.0              # target block temp (°C)

    # --- ΛT definition parameters (from TCHES v1.4) ---
    dT_design_C: float = 15.0          # design ΔT margin
    tau_res_s: float = 390.0           # retention time (18–390s in doc; choose mid)  [s]

    # --- GGZ / plume model (toy) ---
    C_ggz_kJ_per_C: float = 2.0e6       # effective geologic capacitance
    tau_plume_s: float = 3600.0         # plume relaxation time (s)
    plume_limit_C: float = 10.0         # design limit for ΔT_plume
    ggz_frac_base: float = 0.8          # fraction of removed heat sent to GGZ (rest to chillers)

    # --- Ethical symmetry guardrail ---
    Es_min: float = 0.8                # controller throttles if Es < Es_min (doc: alarm <0.8)

    # --- TE toy model (not high fidelity) ---
    dT_TE_target_hi_C: float = 20.0     # doc target window upper end
    te_power_coeff_kW_per_C2: float = 0.12  # P_TE ≈ k*(ΔT_TE^2) (toy)
    te_power_cap_frac: float = 0.12     # cap TE power as fraction of removed heat (5–14% baseline range)

    # --- Pump power (toy) ---
    pump_power_max_kW: float = 25.0

    # --- Control gains ---
    u_min: float = 0.05
    u_max: float = 1.0
    k_load: float = 0.35     # feed-forward on load fraction
    k_temp: float = 0.45     # proportional on temperature error
    k_lambda: float = 0.30   # ΛT feedback gain
    lambda_target: float = 0.7  # doc warn threshold starts at 0.7

    # --- E (model-sensor coupling) proxy ---
    sensor_noise_C: float = 0.2
    model_mismatch_frac: float = 0.03   # mismatch in k_cool for the "twin"
    E_scale_C: float = 6.0              # exp(-|err|/E_scale)

    # --- Transparency proxy ---
    T_ok: float = 0.95
    T_outage: float = 0.65              # <0.7 triggers alarm per doc thresholds


def load_profile(t: float, Q_base_kW: float, Q_peak_kW: float, t_step_s: float, t_drop_s: float) -> float:
    if t < t_step_s:
        return Q_base_kW
    if t < t_drop_s:
        return Q_peak_kW
    return Q_base_kW


def ambient_profile(t: float, T0: float, heatwave_add: float, t_on: float, t_off: float) -> float:
    if t_on <= t < t_off:
        return T0 + heatwave_add
    return T0


def telemetry_ok(t: float, t_out_on: float, t_out_off: float) -> bool:
    return not (t_out_on <= t < t_out_off)


def lambda_T_from_rate(max_abs_dTdt: float, dT_design: float, tau_res: float) -> float:
    # ΛT = max|dT/dt| / (ΔT_design / τ_res)
    denom = dT_design / max(tau_res, 1e-9)
    return max_abs_dTdt / max(denom, 1e-12)


def run(controller: str, out_csv: Path, seed: int, duration_s: int, dt_s: float) -> None:
    rng = np.random.default_rng(seed)
    p = Params()

    # scenario knobs (can be CLI later)
    Q_base = 300.0
    Q_peak = 700.0
    t_step = 600.0
    t_drop = 1800.0

    heatwave_add = 6.0
    t_hw_on = 900.0
    t_hw_off = 1500.0

    t_log_out_on = 1200.0
    t_log_out_off = 1450.0

    # state variables
    T_block = 45.0
    plume = 0.0

    # a simple "digital twin" temperature prediction with slight mismatch
    T_hat = T_block

    # rolling window for |dT/dt| max (streaming approximation of max_t |∂T/∂t|)
    rate_window_s = 120.0
    rate_buf: list[float] = []

    out_csv.parent.mkdir(parents=True, exist_ok=True)
    with out_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "t_s", "controller",
            "Q_load_kW", "T_env_C", "T_block_C", "dTdt_C_per_s",
            "Lambda_T",
            "u_pump", "P_pump_kW",
            "Q_removed_kW", "Q_GGZ_kW", "Q_chiller_kW",
            "dT_TE_C", "P_TE_kW", "Psi_TE",
            "plume_dT_C", "Es_site",
            "E_model", "T_transparency", "Psi_coh", "Psi_total",
            "warn_LambdaT", "alarm_LambdaT",
            "warn_E", "alarm_E",
            "warn_T", "alarm_T",
            "warn_Psi", "alarm_Es"
        ])

        last_T = T_block
        last_dTdt = 0.0

        for step in range(int(duration_s / dt_s) + 1):
            t = step * dt_s

            # exogenous signals
            Q_load = load_profile(t, Q_base, Q_peak, t_step, t_drop)
            T_env = ambient_profile(t, p.T_env_C, heatwave_add, t_hw_on, t_hw_off)
            ok = telemetry_ok(t, t_log_out_on, t_log_out_off)

            # transparency proxy from doc: telemetry/log completeness
            T_trans = p.T_ok if ok else p.T_outage

            # last ΛT estimate for control
            max_abs_rate = max(rate_buf) if rate_buf else abs(last_dTdt)
            Lambda_T = lambda_T_from_rate(max_abs_rate, p.dT_design_C, p.tau_res_s)

            # ethical symmetry from plume (toy; doc defines Es_site from max(...) / design limits)
            Es_site = clamp01(1.0 - (plume / max(p.plume_limit_C, 1e-9)))

            # base pump control (f(load, temp)) + Λ feedback (doc suggests Λ-aware pump control)
            load_frac = Q_load / 500.0  # nominal scaling
            u = p.u_min + p.k_load * load_frac + p.k_temp * ((T_block - p.T_set_C) / p.dT_design_C)

            if controller == "lambda":
                 # Act only when ΛT exceeds target, and push in the direction of temperature error.
                 excess = max(0.0, Lambda_T - p.lambda_target)
                 sign = 1.0 if (T_block - p.T_set_C) >= 0.0 else -1.0
                 u += p.k_lambda * excess * sign


            u = clamp(u, p.u_min, p.u_max)

            # pump power (toy)
            P_pump = p.pump_power_max_kW * (u ** 2)

            # cooling removal
            dT_drive = max(0.0, T_block - T_env)
            Q_removed = p.k_cool_kW_per_C * u * dT_drive
            Q_removed = min(Q_removed, Q_load)  # can't remove more than load in this toy

            # guardrail throttle on GGZ / TE if Es drops below Es_min (doc: throttle if Es_site < Es_min)
            ggz_frac = p.ggz_frac_base
            te_throttle = 1.0
            if Es_site < p.Es_min:
                scale = clamp01(Es_site / max(p.Es_min, 1e-9))
                ggz_frac *= scale
                te_throttle *= scale

            Q_GGZ = ggz_frac * Q_removed
            Q_chiller = Q_removed - Q_GGZ

            # TE model (toy) with ΔT target window idea (doc target ~6–20°C)
            dT_TE = clamp(dT_drive, 0.0, 40.0)
            P_TE = p.te_power_coeff_kW_per_C2 * (dT_TE ** 2)
            P_TE = min(P_TE, p.te_power_cap_frac * Q_removed)
            P_TE *= te_throttle

            # TE utilization proxy: combines ΔT_TE coherence window + capture fraction
            capture_frac = Q_removed / max(Q_load, 1e-9)
            Psi_TE = clamp01((dT_TE / p.dT_TE_target_hi_C) * capture_frac)

            # thermal dynamics (block)
            Q_net = Q_load - Q_removed
            dTdt = Q_net / p.C_block_kJ_per_C  # kW / (kJ/°C) => °C/s
            T_block = T_block + dTdt * dt_s

            # plume dynamics (toy)
            plume = plume + dt_s * ((Q_GGZ / p.C_ggz_kJ_per_C) - (plume / p.tau_plume_s))
            plume = max(0.0, plume)

            # digital-twin mismatch: slightly different cooling gain
            k_hat = p.k_cool_kW_per_C * (1.0 - p.model_mismatch_frac)
            Q_removed_hat = k_hat * u * max(0.0, T_hat - T_env)
            Q_removed_hat = min(Q_removed_hat, Q_load)
            dTdt_hat = (Q_load - Q_removed_hat) / p.C_block_kJ_per_C
            T_hat = T_hat + dTdt_hat * dt_s

            # sensor measurement
            T_meas = T_block + rng.normal(0.0, p.sensor_noise_C)

            # E proxy: model–sensor coupling (doc describes correlation of predicted vs measured patterns; here a 1D proxy)
            E_model = float(math.exp(-abs(T_hat - T_meas) / p.E_scale_C))
            E_model = clamp01(E_model)

            # coherence (lattice style): Psi_coh = E * T
            Psi_coh = E_model * T_trans

            # combined (optional) overall indicator
            Psi_total = Psi_coh * Psi_TE

            # update rate buffer for ΛT max(|dT/dt|)
            abs_rate = abs(dTdt)
            rate_buf.append(abs_rate)
            # keep last ~rate_window_s seconds
            max_len = int(rate_window_s / dt_s)
            if len(rate_buf) > max_len:
                rate_buf = rate_buf[-max_len:]

            # recompute ΛT for logging at this step (using updated window)
            max_abs_rate2 = max(rate_buf)
            Lambda_T = lambda_T_from_rate(max_abs_rate2, p.dT_design_C, p.tau_res_s)

            # alarms / warnings per v1.4 tag table
            warn_L = Lambda_T > 0.7
            alarm_L = Lambda_T > 1.0

            warn_E = E_model < 0.8
            alarm_E = E_model < 0.6

            warn_T = T_trans < 0.85
            alarm_T = T_trans < 0.7

            warn_Psi = Psi_TE < 0.7  # TE utilization proxy
            alarm_Es = Es_site < 0.8

            w.writerow([
                t, controller,
                Q_load, T_env, T_block, dTdt,
                Lambda_T,
                u, P_pump,
                Q_removed, Q_GGZ, Q_chiller,
                dT_TE, P_TE, Psi_TE,
                plume, Es_site,
                E_model, T_trans, Psi_coh, Psi_total,
                int(warn_L), int(alarm_L),
                int(warn_E), int(alarm_E),
                int(warn_T), int(alarm_T),
                int(warn_Psi), int(alarm_Es),
            ])

            last_T = T_block
            last_dTdt = dTdt


def main() -> int:
    ap = argparse.ArgumentParser(description="TCHES reduced-order ODE block sim (ΛT + E/T/Ψ + Es guardrail).")
    ap.add_argument("--controller", choices=["baseline", "lambda"], default="baseline")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--duration_s", type=int, default=2400)
    ap.add_argument("--dt_s", type=float, default=1.0)
    ap.add_argument("--out", type=str, default="python/experiments/tches_ode/out/tches_block.csv")
    args = ap.parse_args()

    out_csv = Path(args.out)
    run(args.controller, out_csv, args.seed, args.duration_s, args.dt_s)
    print(f"Wrote: {out_csv.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
