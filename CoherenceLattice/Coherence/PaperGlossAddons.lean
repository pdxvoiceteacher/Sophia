import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.SacredGeometryLemmasAddons
import CoherenceLattice.Coherence.PhyllotaxisAddons
import CoherenceLattice.Coherence.PhyllotaxisDegreesAddons
import CoherenceLattice.Coherence.PhyllotaxisGeometryAddons
import CoherenceLattice.Coherence.PhyllotaxisNoPeriodAddons
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

theorem Lemma_PhiSquared :
    Coherence.SacredGeometry.phi * Coherence.SacredGeometry.phi
      = Coherence.SacredGeometry.phi + 1 :=
  Coherence.SacredGeometry.phi_sq

theorem Lemma_CenteredHex_2 :
    Coherence.SacredGeometry.centeredHex 2 = 19 := by
  simpa using Coherence.SacredGeometry.centeredHex_2

theorem Lemma_CenteredHex_Succ (n : Nat) :
    Coherence.SacredGeometry.centeredHex (n + 1)
      = Coherence.SacredGeometry.centeredHex n + 6 * (n + 1) :=
  Coherence.SacredGeometryLemmas.centeredHex_succ n

theorem Lemma_RatioFourth_lt_RatioFifth :
    Coherence.SacredGeometry.ratioFourth < Coherence.SacredGeometry.ratioFifth :=
  Coherence.SacredGeometryLemmas.ratioFourth_lt_ratioFifth

theorem Lemma_RatioFifth_lt_RatioOctave :
    Coherence.SacredGeometry.ratioFifth < Coherence.SacredGeometry.ratioOctave :=
  Coherence.SacredGeometryLemmas.ratioFifth_lt_ratioOctave

theorem Lemma_TurnFracBounds (n : Nat) :
    And (0 <= Coherence.Phyllotaxis.turnFrac n) (Coherence.Phyllotaxis.turnFrac n < 1) := by
  -- turnFrac_bounds returns the same statement; use simp to convert notation
  simpa [And] using Coherence.Phyllotaxis.turnFrac_bounds n

theorem Lemma_AngleBounds (n : Nat) :
    And (0 <= Coherence.Phyllotaxis.angle n) (Coherence.Phyllotaxis.angle n < (2 * Real.pi)) := by
  simpa [And] using Coherence.Phyllotaxis.angle_bounds n

theorem Lemma_PointOnUnitCircle (n : Nat) :
    (Coherence.PhyllotaxisGeometry.px n) ^ 2 + (Coherence.PhyllotaxisGeometry.py n) ^ 2 = 1 :=
  Coherence.PhyllotaxisGeometry.point_on_unit_circle n

theorem Lemma_PointCoordBounds (n : Nat) :
    And (-1 <= Coherence.PhyllotaxisGeometry.px n ∧ Coherence.PhyllotaxisGeometry.px n <= 1)
        (-1 <= Coherence.PhyllotaxisGeometry.py n ∧ Coherence.PhyllotaxisGeometry.py n <= 1) := by
  simpa [And] using Coherence.PhyllotaxisGeometry.point_coord_bounds n

theorem Theorem_NoFixedExponentExample :
    Not (Exists fun b : Real =>
      And (Coherence.BetaRefutation.systemHigh.M =
            Coherence.BetaRefutation.systemHigh.I ^ b)
          (Coherence.BetaRefutation.systemLow.M =
            Coherence.BetaRefutation.systemLow.I ^ b)) :=
  Coherence.BetaRefutation.no_fixed_b_example

theorem Lemma_TAF_Unfold
    (phi : Coherence.TAF.Phi) (x : Coherence.TAF.XSt) (a : Coherence.TAF.Agent) :
    Coherence.TAF.S_total phi x a
      = Coherence.TAF.S_theta phi + Coherence.TAF.S_info phi x + Coherence.TAF.S_coh x a := by
  simpa using Coherence.TAF.S_total_unfold phi x a

theorem Theorem_NoShortPeriod
    (hirr : Irrational Coherence.Phyllotaxis.goldenTurn)
    (n k : Nat)
    (h : Coherence.Phyllotaxis.turnFrac (n + k) = Coherence.Phyllotaxis.turnFrac n) :
    k = 0 :=
  Coherence.PhyllotaxisNoPeriod.no_short_period hirr n k h

/-- (Paper Lemma) Golden angle in degrees: 360 * (1 - 1/phi). -/
theorem Lemma_GoldenAngleDegrees :
    Coherence.PhyllotaxisDegrees.goldenAngleDeg
      = 360 * (1 - 1 / Coherence.SacredGeometry.phi) :=
  Coherence.PhyllotaxisDegrees.goldenAngleDeg_formula

/-- (Paper Lemma) Degree/radian consistency for golden angle. -/
theorem Lemma_GoldenAngleDegToRad :
    Coherence.PhyllotaxisDegrees.degToRad Coherence.PhyllotaxisDegrees.goldenAngleDeg
      = Coherence.PhyllotaxisDegrees.goldenAngleRad :=
  Coherence.PhyllotaxisDegrees.degToRad_goldenAngle

end
end PaperGloss
end Coherence