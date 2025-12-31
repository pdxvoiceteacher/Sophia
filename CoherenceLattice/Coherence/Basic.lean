import Mathlib

set_option linter.style.commandStart false

namespace Coherence

/-- Empathy E and Transparency T live in [0,1]. -/
structure CoherenceInput where
  E : ℝ
  T : ℝ
  hE0 : 0 ≤ E
  hE1 : E ≤ 1
  hT0 : 0 ≤ T
  hT1 : T ≤ 1

/-- Coherence Ψ = E * T. -/
def psi (x : CoherenceInput) : ℝ := x.E * x.T

lemma psi_nonneg (x : CoherenceInput) : 0 ≤ psi x := by
  unfold psi
  exact mul_nonneg x.hE0 x.hT0

lemma psi_le_one (x : CoherenceInput) : psi x ≤ 1 := by
  unfold psi
  have hET_le_E : x.E * x.T ≤ x.E := by
    exact mul_le_of_le_one_right x.hE0 x.hT1
  exact le_trans hET_le_E x.hE1

lemma psi_bounds (x : CoherenceInput) : 0 ≤ psi x ∧ psi x ≤ 1 :=
  ⟨psi_nonneg x, psi_le_one x⟩

/-- Parameters for ΔSyn: ΔS = −lam ∇H − mu Eₛ -/
structure DeltaSynInput where
  lam : ℝ
  mu : ℝ
  gradH : ℝ
  Es : ℝ
  hlam0 : 0 ≤ lam
  hmu0 : 0 ≤ mu

def deltaS (x : DeltaSynInput) : ℝ :=
  -(x.lam * x.gradH) - (x.mu * x.Es)

lemma deltaS_nonpos_of_nonneg (x : DeltaSynInput)
    (hgradH : 0 ≤ x.gradH) (hEs : 0 ≤ x.Es) :
    deltaS x ≤ 0 := by
  have h1 : -(x.lam * x.gradH) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg x.hlam0 hgradH)
  have h2 : -(x.mu * x.Es) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg x.hmu0 hEs)
  have : -(x.lam * x.gradH) + (-(x.mu * x.Es)) ≤ 0 := add_nonpos h1 h2
  simpa [deltaS, sub_eq_add_neg] using this

/-- If ∇H = 0 and mu > 0 and Eₛ > 0 then ΔS < 0. -/
lemma deltaS_neg_of_Es_pos_gradH_zero (x : DeltaSynInput)
    (hmuPos : 0 < x.mu) (hgrad : x.gradH = 0) (hEsPos : 0 < x.Es) :
    deltaS x < 0 := by
  have hx : deltaS x = -(x.mu * x.Es) := by
    simp [deltaS, hgrad]
  have hmul : 0 < x.mu * x.Es := mul_pos hmuPos hEsPos
  have hneg : -(x.mu * x.Es) < 0 := neg_neg_of_pos hmul
  simpa [hx] using hneg

/-- If ∇H = 0 and mu > 0 and Eₛ < 0 then ΔS > 0. -/
lemma deltaS_pos_of_Es_neg_gradH_zero (x : DeltaSynInput)
    (hmuPos : 0 < x.mu) (hgrad : x.gradH = 0) (hEsNeg : x.Es < 0) :
    deltaS x > 0 := by
  have hx : deltaS x = -(x.mu * x.Es) := by
    simp [deltaS, hgrad]
  have hmul : x.mu * x.Es < 0 := mul_neg_of_pos_of_neg hmuPos hEsNeg
  have hpos : 0 < -(x.mu * x.Es) := neg_pos.mpr hmul
  have : 0 < deltaS x := by
    simpa [hx] using hpos
  exact this

end Coherence