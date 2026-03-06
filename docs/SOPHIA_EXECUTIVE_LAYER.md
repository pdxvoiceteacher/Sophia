# Sophia Executive Layer Contract

Sophia is the canonical executive cognition layer for adaptive weighting.

## Governance pipeline (phaselock order)

All adaptive weighting must flow through this strict sequence:

**CoherenceLattice -> Sophia -> Publisher**

Not an arbitrary bidirectional loop.

## Shared artifact semantics

- **formal drift** = **CoherenceLattice truth**.
- **attention update** = **Sophia executive interpretation**.
- **overlay rendering** = **Publisher visualization / memory presentation**.

## Operational requirement

Publisher should not invent executive weighting logic independently. Publisher consumes Sophia bridge artifacts and applies the overlay faithfully.

## Naming recommendation

If Publisher keeps a local visual mismatch comparator, name it something explicit like:

- `activityMismatchScore`

This avoids conflating local rendering diagnostics with canonical lattice-derived drift.
