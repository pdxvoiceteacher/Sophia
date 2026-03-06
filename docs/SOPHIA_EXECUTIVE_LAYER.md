# Sophia Executive Layer Contract

Sophia is the canonical executive cognition layer for adaptive weighting.

## Governance pipeline

All adaptive weighting must flow through the following sequence:

**CoherenceLattice truth -> Sophia evaluation -> Publisher overlay**

- **CoherenceLattice truth**: formal coherence and drift outputs (`coherence_assessment`, `coherence_drift_map`, regime maps).
- **Sophia evaluation**: transforms formal metrics into deterministic, explainable attention updates (`attention_updates.json`).
- **Publisher overlay**: renders and presents these updates without inventing independent executive weighting logic.

## Operational requirement

Publisher should not create executive weighting rules independently. It should consume Sophia bridge artifacts and apply the overlay faithfully.
