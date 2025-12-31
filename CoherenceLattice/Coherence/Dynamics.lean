import CoherenceLattice.Coherence.Basic
import CoherenceLattice.Coherence.NoTeleport

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false
set_option linter.unusedSimpArgs false
noncomputable section

/-- Clamp a real to the unit interval [0,1]. -/
def clamp01Real (x : ℝ) : ℝ :=
  max 0 (min x 1)

lemma clamp01Real_nonneg (x : ℝ) : 0 ≤ clamp01Real x := by
  unfold clamp01Real
  exact le_max_left _ _

lemma clamp01Real_le_one (x : ℝ) : clamp01Real x ≤ 1 := by
  unfold clamp01Real
  refine (max_le_iff).2 ?_
  constructor
  · norm_num
  · exact min_le_right _ _

lemma clamp01Real_bounds (x : ℝ) : 0 ≤ clamp01Real x ∧ clamp01Real x ≤ 1 :=
  ⟨clamp01Real_nonneg x, clamp01Real_le_one x⟩

/--
If x ∈ [0,1], then clamping (x+c) to [0,1] moves it by at most |c|.
(We prove this by cases: x+c ≤ 0, 1 ≤ x+c, or 0 < x+c < 1.)
-/
lemma abs_clamp01Real_add_sub_le_abs {x c : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |clamp01Real (x + c) - x| ≤ |c| := by
  by_cases h0 : x + c ≤ 0
  · -- clamp = 0
    have hclamp : clamp01Real (x + c) = 0 := by
      unfold clamp01Real
      have hmin : min (x + c) 1 = x + c := by
        refine min_eq_left ?_
        linarith [h0]
      have hmax : max 0 (x + c) = 0 := max_eq_left h0
      simp [hmin, hmax]
    have hx_le_negc : x ≤ -c := by linarith [h0]
    have hnegc_le_absc : -c ≤ |c| := by
      have : -c ≤ |-c| := le_abs_self (-c)
      simpa [abs_neg] using this
    have hx_le_absc : x ≤ |c| := le_trans hx_le_negc hnegc_le_absc
    have habs : |clamp01Real (x + c) - x| = x := by
      simp [hclamp, hx0]
    simpa [habs] using hx_le_absc
  · have h0lt : 0 < x + c := lt_of_not_ge h0
    by_cases h1 : 1 ≤ x + c
    · -- clamp = 1
      have hclamp : clamp01Real (x + c) = 1 := by
        unfold clamp01Real
        have hmin : min (x + c) 1 = (1 : ℝ) := min_eq_right h1
        simp [hmin]
      have hc : 1 - x ≤ c := by linarith [h1]
      have hnonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have hbound : |1 - x| ≤ |c| := by
        have : 1 - x ≤ |c| := le_trans hc (le_abs_self c)
        simpa [abs_of_nonneg hnonneg] using this
      have habs : |clamp01Real (x + c) - x| = |1 - x| := by
        simp [hclamp]
      simpa [habs] using hbound
    · -- 0 < x+c and x+c < 1 => clamp = x+c
      have h1lt : x + c < 1 := lt_of_not_ge h1
      have hclamp : clamp01Real (x + c) = x + c := by
        unfold clamp01Real
        have hmin : min (x + c) 1 = x + c := min_eq_left h1lt.le
        have hmax : max 0 (x + c) = x + c := max_eq_right h0lt.le
        simp [hmin, hmax]
      have habs : |clamp01Real (x + c) - x| = |c| := by
        simp [hclamp]
      simpa [habs] using (le_rfl : |c| ≤ |c|)

/-- Convert a ψ in [0,1] into a lattice State with T=1. -/
def stateOfPsi (ψ : ℝ) (h0 : 0 ≤ ψ) (h1 : ψ ≤ 1) : State :=
  (⟨ψ, ⟨h0, h1⟩⟩, ⟨1, ⟨by norm_num, by norm_num⟩⟩)

@[simp] lemma psi_stateOfPsi (ψ : ℝ) (h0 : 0 ≤ ψ) (h1 : ψ ≤ 1) :
    psi (stateOfPsi ψ h0 h1) = ψ := by
  simp [psi, E, T, stateOfPsi]

/-- ΔSyn-driven raw ψ increment. -/
def deltaPsi (η : ℝ) (p : Coherence.DeltaSynInput) : ℝ :=
  η * (-Coherence.deltaS p)

/-- Cap any increment to ±(tau0/2) so the classifier can't jump more than one step. -/
def capDelta (δ : ℝ) : ℝ :=
  max (-(tau0 / 2)) (min δ (tau0 / 2))

lemma capDelta_le (δ : ℝ) : capDelta δ ≤ (tau0 / 2) := by
  unfold capDelta
  refine (max_le_iff).2 ?_
  constructor
  · have hpos : 0 ≤ tau0 / 2 := by
      unfold tau0; norm_num
    linarith
  · exact min_le_right _ _

lemma neg_capDelta_le (δ : ℝ) : -(tau0 / 2) ≤ capDelta δ := by
  unfold capDelta
  exact le_max_left _ _

lemma abs_capDelta_le (δ : ℝ) : |capDelta δ| ≤ (tau0 / 2) := by
  apply abs_le.2
  constructor
  · exact neg_capDelta_le δ
  · exact capDelta_le δ

/-- ΔSyn step on ψ (capped), lifted back into a State with T=1. -/
def stepPsi (η : ℝ) (p : Coherence.DeltaSynInput) (s : State) : State :=
  let c := capDelta (deltaPsi η p)
  let ψ2 := clamp01Real (psi s + c)
  have h0 : 0 ≤ ψ2 := (clamp01Real_bounds (psi s + c)).1
  have h1 : ψ2 ≤ 1 := (clamp01Real_bounds (psi s + c)).2
  stateOfPsi ψ2 h0 h1

/--
Capped ΔSyn step is always a valid regime transition (no teleport),
because ψ moves by < τ₀ and we can apply the NoTeleport theorem.
-/
theorem validTransition_stepPsi (η : ℝ) (p : Coherence.DeltaSynInput) (s : State) :
    validTransition s (stepPsi η p s) := by
  have hx : 0 ≤ psi s ∧ psi s ≤ 1 := psi_bounds s
  let c := capDelta (deltaPsi η p)
  let ψ2 := clamp01Real (psi s + c)

  have hψ2 : psi (stepPsi η p s) = ψ2 := by
    simp [stepPsi, ψ2, c, clamp01Real_bounds]

  have hmove : |ψ2 - psi s| ≤ |c| := by
    have := abs_clamp01Real_add_sub_le_abs (x := psi s) (c := c) hx.1 hx.2
    simpa [ψ2] using this

  have hcap : |c| ≤ (tau0 / 2) := by
    simpa [c] using abs_capDelta_le (deltaPsi η p)

  have hle : |ψ2 - psi s| ≤ (tau0 / 2) := le_trans hmove hcap

  have ht : (tau0 / 2) < tau0 := by
    unfold tau0; norm_num

  have habs : |psi (stepPsi η p s) - psi s| < tau0 := by
    have hlt : |ψ2 - psi s| < tau0 := lt_of_le_of_lt hle ht
    simpa [hψ2] using hlt

  exact validTransition_of_abs_lt_tau0 (s₁ := s) (s₂ := stepPsi η p s) habs

end  -- noncomputable section

end Lattice
end Coherence