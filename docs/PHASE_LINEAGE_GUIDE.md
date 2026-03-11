# Phase Lineage Guide (LRQ v0.1)

This guide is a **legibility and queryability hardening artifact**, not a constitutional or cosmological phase.

## Purpose

The triadic bridge architecture has grown across many bounded phases. This guide helps stewards:

- locate upstream and downstream artifacts quickly,
- understand what constraints are preserved versus transformed,
- query large artifacts without founder-only context,
- keep interpretation non-authoritative and reviewable.

## Primary LRQ Artifacts

- `bridge/phase_lineage_registry.json`
- `bridge/phase_glossary.json`
- `bridge/coherence_memory_trace.json`

These artifacts are deterministic, machine-readable, and bounded. They do **not** authorize governance transfer, canon closure, centralized successor rule, or epoch authority.

## How to Read Lineage

1. Start with a `phaseId` in `phase_lineage_registry.json`.
2. Check `upstreamArtifacts` and `downstreamArtifacts`.
3. Inspect `preservedConstraints` and `canonicalBoundaryNote`.
4. Use `coherence_memory_trace.json` for compressed carried-forward invariants and unresolved tensions.
5. Use helper tools for slicing:
   - `python -m coherence.tools.query_bridge_artifact ...`
   - `python -m coherence.tools.summarize_phase_status ...`

## Boundary Reminder

Recommendations in lineage artifacts are bounded guidance only and do not declare final epochs, authorize settlement, or canonize emergent civilizational assumptions.
