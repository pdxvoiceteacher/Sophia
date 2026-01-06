import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.SacredGeometryLemmasAddons
import CoherenceLattice.Coherence.PhyllotaxisDegreesAddons
import CoherenceLattice.Coherence.PhyllotaxisGeometryAddons
import CoherenceLattice.Coherence.PhyllotaxisNoPeriodAddons
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons
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

theorem Lemma_CenteredHex_Succ (n : Nat) :
    Coherence.SacredGeometry.centeredHex (n + 1)
      = Coherence.SacredGeometry.centeredHex n + 6 * (n + 1) :=
  Coherence.SacredGeometryLemmas.centeredHex_succ n

theorem Lemma_GoldenAngleDegrees :
    Coherence.PhyllotaxisDegrees.goldenAngleDeg
      = 360 * (1 - 1 / Coherence.SacredGeometry.phi) :=
  Coherence.PhyllotaxisDegrees.goldenAngleDeg_formula

theorem Lemma_GoldenAngleDegToRad :
    Coherence.PhyllotaxisDegrees.degToRad Coherence.PhyllotaxisDegrees.goldenAngleDeg
      = Coherence.PhyllotaxisDegrees.goldenAngleRad :=
  Coherence.PhyllotaxisDegrees.degToRad_goldenAngle

theorem Lemma_PointOnUnitCircle (n : Nat) :
    (Coherence.PhyllotaxisGeometry.px n) ^ 2 + (Coherence.PhyllotaxisGeometry.py n) ^ 2 = 1 :=
  Coherence.PhyllotaxisGeometry.point_on_unit_circle n

theorem Lemma_TAF_Unfold
    (phi : Coherence.TAF.Phi) (x : Coherence.TAF.XSt) (a : Coherence.TAF.Agent) :
    Coherence.TAF.S_total phi x a
      = Coherence.TAF.S_theta phi + Coherence.TAF.S_info phi x + Coherence.TAF.S_coh x a := by
  simpa using Coherence.TAF.S_total_unfold phi x a

theorem Lemma_DiskNormSq (n N : Nat) :
    (Coherence.PhyllotaxisDisk.px n N) ^ 2 + (Coherence.PhyllotaxisDisk.py n N) ^ 2
      = (Coherence.PhyllotaxisDisk.radius n N) ^ 2 :=
  Coherence.PhyllotaxisDisk.normSq_eq_radiusSq n N

theorem Lemma_DiskInUnitDisk (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PhyllotaxisDisk.px n N) ^ 2 + (Coherence.PhyllotaxisDisk.py n N) ^ 2 <= 1 := by
  have hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  exact Coherence.PhyllotaxisDisk.normSq_le_one_of_le n N hN0' hn

/-- (Paper Lemma) Radius monotonicity: if n1 ≤ n2 ≤ N and N≠0 then r(n1) ≤ r(n2). -/
theorem Lemma_RadiusMonotone (n1 n2 N : Nat) (hN0 : N = 0 -> False)
    (h12 : n1 <= n2) (h2N : n2 <= N) :
    Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N := by
  have hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  -- h2N is included to match the paper statement "n1 ≤ n2 ≤ N"
  exact Coherence.PhyllotaxisDisk.radius_mono_of_le n1 n2 N hN0' h12

theorem Theorem_NoShortPeriod
    (hirr : Irrational Coherence.Phyllotaxis.goldenTurn)
    (n k : Nat)
    (h : Coherence.Phyllotaxis.turnFrac (n + k) = Coherence.Phyllotaxis.turnFrac n) :
    k = 0 :=
  Coherence.PhyllotaxisNoPeriod.no_short_period hirr n k h

end
end PaperGloss
end Coherence