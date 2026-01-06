import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.SacredGeometryLemmasAddons
import CoherenceLattice.Coherence.PhyllotaxisAddons
import CoherenceLattice.Coherence.PhyllotaxisGeometryAddons
import CoherenceLattice.Coherence.BetaRefutationAddons
import CoherenceLattice.Coherence.TotalActionFunctionalAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons

Paper-facing lemma names for manuscript citation (no new theory).
-/

/-- (Paper Lemma) Golden ratio identity: phi^2 = phi + 1. -/
theorem Lemma_PhiSquared :
    Coherence.SacredGeometry.phi * Coherence.SacredGeometry.phi
      = Coherence.SacredGeometry.phi + 1 :=
  Coherence.SacredGeometry.phi_sq

/-- (Paper Lemma) Centered hex number at n=2 is 19. -/
theorem Lemma_CenteredHex_2 :
    Coherence.SacredGeometry.centeredHex 2 = 19 := by
  simpa using Coherence.SacredGeometry.centeredHex_2

/-- (Paper Lemma) Centered-hex recurrence: N(n+1)=N(n)+6(n+1). -/
theorem Lemma_CenteredHex_Succ (n : Nat) :
    Coherence.SacredGeometry.centeredHex (n + 1)
      = Coherence.SacredGeometry.centeredHex n + 6 * (n + 1) :=
  Coherence.SacredGeometryLemmas.centeredHex_succ n

/-- (Paper Lemma) Interval ordering: 4/3 < 3/2. -/
theorem Lemma_RatioFourth_lt_RatioFifth :
    Coherence.SacredGeometry.ratioFourth < Coherence.SacredGeometry.ratioFifth :=
  Coherence.SacredGeometryLemmas.ratioFourth_lt_ratioFifth

/-- (Paper Lemma) Interval ordering: 3/2 < 2. -/
theorem Lemma_RatioFifth_lt_RatioOctave :
    Coherence.SacredGeometry.ratioFifth < Coherence.SacredGeometry.ratioOctave :=
  Coherence.SacredGeometryLemmas.ratioFifth_lt_ratioOctave

/-- (Paper Lemma) turnFrac is always in [0,1). -/
theorem Lemma_TurnFracBounds (n : Nat) :
    0 ≤ Coherence.Phyllotaxis.turnFrac n ∧ Coherence.Phyllotaxis.turnFrac n < 1 :=
  Coherence.Phyllotaxis.turnFrac_bounds n

/-- (Paper Lemma) angle is always in [0,2*pi). -/
theorem Lemma_AngleBounds (n : Nat) :
    0 ≤ Coherence.Phyllotaxis.angle n ∧ Coherence.Phyllotaxis.angle n < (2 * Real.pi) :=
  Coherence.Phyllotaxis.angle_bounds n

/-- (Paper Lemma) Phyllotaxis point lies on unit circle: x^2 + y^2 = 1. -/
theorem Lemma_PointOnUnitCircle (n : Nat) :
    (Coherence.PhyllotaxisGeometry.px n) ^ 2 + (Coherence.PhyllotaxisGeometry.py n) ^ 2 = 1 :=
  Coherence.PhyllotaxisGeometry.point_on_unit_circle n

/-- (Paper Lemma) Phyllotaxis point coordinates are within [-1,1]. -/
theorem Lemma_PointCoordBounds (n : Nat) :
    (-1 ≤ Coherence.PhyllotaxisGeometry.px n ∧ Coherence.PhyllotaxisGeometry.px n ≤ 1) ∧
    (-1 ≤ Coherence.PhyllotaxisGeometry.py n ∧ Coherence.PhyllotaxisGeometry.py n ≤ 1) :=
  Coherence.PhyllotaxisGeometry.point_coord_bounds n

/-- (Paper Theorem) No fixed exponent b satisfies M = I^b for both example systems. -/
theorem Theorem_NoFixedExponentExample :
    ¬ ∃ b : ℝ,
        Coherence.BetaRefutation.systemHigh.M =
          Coherence.BetaRefutation.systemHigh.I ^ b ∧
        Coherence.BetaRefutation.systemLow.M =
          Coherence.BetaRefutation.systemLow.I ^ b :=
  Coherence.BetaRefutation.no_fixed_b_example

/-- (Paper Lemma) Total Action Functional unfolds into its component sum. -/
theorem Lemma_TAF_Unfold
    (phi : Coherence.TAF.Phi) (x : Coherence.TAF.XSt) (a : Coherence.TAF.Agent) :
    Coherence.TAF.S_total phi x a
      = Coherence.TAF.S_theta phi + Coherence.TAF.S_info phi x + Coherence.TAF.S_coh x a := by
  simpa using Coherence.TAF.S_total_unfold phi x a

end
end PaperGloss
end Coherence