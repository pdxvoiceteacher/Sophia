import CoherenceLattice.Coherence.Interpretation

/-!
# Narrative Gloss (Paper Alignment)

This file is *not* new theory; it is a curated “gloss” that maps the Lean formalization
to paper-facing statements and section headings.

## Core objects

- `Coherence.Lattice.State` : a coherence state (E,T) ∈ [0,1]×[0,1].
- `Coherence.Lattice.psi`   : Ψ(E,T) := E*T, bounded in [0,1].
- `Coherence.Regime`        : discrete regimes S0..S4.
- `Coherence.Lattice.classify` : assigns a regime by Ψ-bands (τ0..τ3).
- `Coherence.adj`           : allowed regime transitions (neighbor steps + self).

## Safety spine (graph-compatibility)

- `validTransition` says: the regime of the next state lies in the adjacency list of the current regime.
- `validTransition_of_abs_lt_tau0` says: if |ΔΨ| < τ0 then the transition is valid (no teleport).
- `validPath_traj*` lemmas lift one-step validity to multi-step regime paths.

## Dynamics

We provide two dynamics models:

1) **ψ-centric step** `stepPsi` (ΔSyn-driven, capped, clamped) with theorem:
   - `validTransition_stepPsi` : always a valid regime transition.

2) **E/T-centric step** `stepET` (ΔSyn-driven on E and T directly, capped, clamped) with theorems:
   - `validTransition_stepET` : always a valid regime transition.
   - `abs_psi_stepET_sub_le`  : bounded per-step drift, |ΔΨ| ≤ τ0/2.
   - `psi_stepET_nondec_of_deltaS_neg` :
       if ΔS < 0 and ηE,ηT ≥ 0, then Ψ does not decrease.

These are the formal “guardrail” statements you can cite in the manuscript.
-/

namespace Coherence
namespace PaperGloss

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.unusedSimpArgs false
noncomputable section

open Coherence
open Coherence.Lattice

/-!
## Paper-named lemma wrappers

These wrappers exist so your manuscript can cite stable, human-readable lemma names
without digging through internal file organization.
-/

/-- (Paper Lemma) Negative ΔS implies positive drive. -/
theorem Lemma_DrivePositive
    (p : Coherence.DeltaSynInput) (hΔS : Coherence.deltaS p < 0) :
    0 < Coherence.Lattice.drive p :=
  Coherence.Lattice.drive_pos_of_deltaS_neg p hΔS

/-- (Paper Lemma) Bounded drift per E/T step: |ΔΨ| ≤ τ0/2. -/
theorem Lemma_BoundedDrift_stepET
    (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : Coherence.Lattice.State) :
    |Coherence.Lattice.psi (Coherence.Lattice.stepET ηE ηT p s) - Coherence.Lattice.psi s|
      ≤ (Coherence.Lattice.tau0 / 2) :=
  Coherence.Lattice.abs_psi_stepET_sub_le ηE ηT p s

/--
(Paper Lemma) If ΔS < 0 and ηE,ηT ≥ 0, then Ψ is non-decreasing under stepET.
This is the “interpretation lemma” that connects ΔSyn descent to coherence ascent (under caps).
-/
theorem Lemma_PsiNondecreasing_stepET
    (ηE ηT : ℝ) (hηE : 0 ≤ ηE) (hηT : 0 ≤ ηT)
    (p : Coherence.DeltaSynInput) (hΔS : Coherence.deltaS p < 0)
    (s : Coherence.Lattice.State) :
    Coherence.Lattice.psi s ≤ Coherence.Lattice.psi (Coherence.Lattice.stepET ηE ηT p s) :=
  Coherence.Lattice.psi_stepET_nondec_of_deltaS_neg ηE ηT hηE hηT p hΔS s

/-- (Paper Theorem) No teleport: if |ΔΨ| < τ0 then the induced regime transition is valid. -/
theorem Theorem_NoTeleport
    {s₁ s₂ : Coherence.Lattice.State} (h : |Coherence.Lattice.psi s₂ - Coherence.Lattice.psi s₁| < Coherence.Lattice.tau0) :
    Coherence.Lattice.validTransition s₁ s₂ :=
  Coherence.Lattice.validTransition_of_abs_lt_tau0 (s₁ := s₁) (s₂ := s₂) h

/-- (Paper Theorem) ΔSyn ψ-step always respects the regime graph. -/
theorem Theorem_DeltaSynPsiStep_Safe
    (η : ℝ) (p : Coherence.DeltaSynInput) (s : Coherence.Lattice.State) :
    Coherence.Lattice.validTransition s (Coherence.Lattice.stepPsi η p s) :=
  Coherence.Lattice.validTransition_stepPsi η p s

/-- (Paper Theorem) ΔSyn E/T-step always respects the regime graph. -/
theorem Theorem_DeltaSynETStep_Safe
    (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : Coherence.Lattice.State) :
    Coherence.Lattice.validTransition s (Coherence.Lattice.stepET ηE ηT p s) :=
  Coherence.Lattice.validTransition_stepET ηE ηT p s

/--
(Paper Corollary) Iterating stepET produces a regime sequence that is a valid path in the regime graph.
-/
theorem Corollary_TrajectoryET_ValidPath
    (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) :
    ∀ n s, Coherence.validPath (Coherence.Lattice.regimePath (Coherence.Lattice.trajET ηE ηT p n s)) :=
  Coherence.Lattice.validPath_trajET ηE ηT p

end
end PaperGloss
end Coherence