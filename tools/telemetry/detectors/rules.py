from __future__ import annotations


def entropy_spike_rule(value: float, cut: float) -> bool:
    return float(value) >= float(cut)


def no_teleport_rule(delta_psi: float, tau0: float) -> bool:
    return float(delta_psi) <= float(tau0)


def branch_divergence_rule(delta_factor: float, delta_nodes: int, warn_factor: float, warn_nodes: int) -> bool:
    return abs(float(delta_factor)) > float(warn_factor) or abs(int(delta_nodes)) >= int(warn_nodes)
