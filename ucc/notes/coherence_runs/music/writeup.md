# Coherence Music (Bhairav GUFT demo) — Strict Writeup

## What this run is
This run generates a Bhairav-based phrase sequence using the `CoherenceMusicEngine`.
At each timestep, the engine selects a **phrase category** (`E`, `T`, `PSI`, `DELTA_S`, `E_SYM`, `LAMBDA`, or `BASE`)
using **weighted sampling** derived from the input metric series.

## What we claim (and how to verify)
We claim that:
1) The engine emits non-BASE categories (coverage > 0).
2) Category selection shows **lift**: when a category is selected, its corresponding metric tends to be higher
   (quantified as `lift = mean(metric | category) / mean(metric overall)` in `*_audit_summary.json`).
3) The run is auditable end-to-end via:
   - trace.json/trace.csv (step aligned)
   - audit_summary.json/audit_summary.md
   - UCC wrapper artifact JSON
   - evidence links to the repo.

## Limitations
- This is a toy demonstration, not a scientific claim about cognition.
- Lift is descriptive and not a causal proof.
- Semitone quantization: no microtonal encoding in this minimal engine.

## Disclosure
Research scaffold only. No operational / clinical / legal use.

## Assumptions
- Metric series are normalized to ~[0,1] and aligned step-for-step with generated phrases.
- Category weights increase monotonically with their corresponding metric.

## Uncertainty
- Weighted sampling introduces randomness; deterministic when seed is fixed.
- Lift is descriptive; it does not prove causality.
