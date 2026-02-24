"""Detector stubs for declared epoch analysis algorithms.

These functions intentionally remain lightweight and deterministic.
"""

from .rules import branch_divergence_rule, entropy_spike_rule, no_teleport_rule

__all__ = ["branch_divergence_rule", "entropy_spike_rule", "no_teleport_rule"]
