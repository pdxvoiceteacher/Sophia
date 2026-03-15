"""Kernel modules for triadic-brain coherence orchestration."""

from .evolution_engine import EvolutionEngine
from .renormalization import coarse_grain, renormalize

__all__ = ["EvolutionEngine", "coarse_grain", "renormalize"]
