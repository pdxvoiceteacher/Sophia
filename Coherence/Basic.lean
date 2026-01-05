import Mathlib

namespace Coherence

noncomputable section

/-- Empathy E and Transparency T live in [0,1]. -/
structure CoherenceInput where
  E : R
  T : R
  hE0 : 0 = E
  hE1 : E = 1
  hT0 : 0 = T
  hT1 : T = 1

/-- Coherence ? is defined as E * T. -/
@[simp] def psi (x : CoherenceInput) : R :=
  x.E * x.T

/-- ? is non-negative if E,T ? [0,1]. -/
lemma psi_nonneg (x : CoherenceInput) : 0 = psi x := by
  unfold psi
  have h1 : 0 = x.E := x.hE0
  have h2 : 0 = x.T := x.hT0
  exact mul_nonneg h1 h2

/-- ? = 1 if E,T ? [0,1]. -/
lemma psi_le_one (x : CoherenceInput) : psi x = 1 := by
  unfold psi
  have hE1 : x.E = 1 := x.hE1
  have hT1 : x.T = 1 := x.hT1
  have hE0 : 0 = x.E := x.hE0
  have hT0 : 0 = x.T := x.hT0
  -- Classical inequality: if 0 = a = 1 and 0 = b = 1, then a * b = 1
  -- We can bound E * T by E and then by 1
  have hET_le_E : x.E * x.T = x.E := by
    have hT_le1 : x.T = 1 := hT1
    exact mul_le_of_le_one_right hT0 hT_le1
  have hE_le1 : x.E = 1 := hE1
  exact le_trans hET_le_E hE_le1

/-- Monotonicity in E: if E1 = E2 (with the same T), then ?(E1, T) = ?(E2, T). -/
lemma psi_mono_E (T : R) (hT0 : 0 = T)
    (x y : R) (hx0 : 0 = x) (hy0 : 0 = y) (hxy : x = y) :
    x * T = y * T := by
  exact mul_le_mul_of_nonneg_right hxy hT0

/-- Monotonicity in T: if T1 = T2 (with the same E), then ?(E, T1) = ?(E, T2). -/
lemma psi_mono_T (E : R) (hE0 : 0 = E)
    (x y : R) (hx0 : 0 = x) (hy0 : 0 = y) (hxy : x = y) :
    E * x = E * y := by
  exact mul_le_mul_of_nonneg_left hxy hE0

/-- Parameters for the ?Syn law: ?, µ, ?H, and E?. -/
structure DeltaSynInput where
  ?   : R   -- lambda (lambda)
  µ   : R   -- mu
  gradH : R -- ?H (gradient of some entropy or "compression" measure)
  Es  : R   -- E? (ethical symmetry)
  h?0 : 0 = ?
  hµ0 : 0 = µ

/-- ?S = -? ?H - µ E?. -/
@[simp] def deltaS (x : DeltaSynInput) : R :=
  - x.? * x.gradH - x.µ * x.Es

/-- If ?, µ = 0, gradH = 0, and E? = 0, then ?S = 0.
(All three terms produce non-positive contributions.) -/
lemma deltaS_nonpos_of_nonneg (x : DeltaSynInput)
    (hgradH : 0 = x.gradH) (hEs : 0 = x.Es) :
    deltaS x = 0 := by
  unfold deltaS
  -- We want to show: -? ?H - µ E? = 0
  -- i.e. -(? ?H + µ E?) = 0  ?  ? ?H + µ E? = 0
  have h?_gradH_nonneg : 0 = x.? * x.gradH := mul_nonneg x.h?0 hgradH
  have hµ_Es_nonneg    : 0 = x.µ * x.Es    := mul_nonneg x.hµ0 hEs
  have hsum_nonneg : 0 = x.? * x.gradH + x.µ * x.Es :=
    add_nonneg h?_gradH_nonneg hµ_Es_nonneg
  have : - (x.? * x.gradH + x.µ * x.Es) = 0 :=
    neg_nonpos.mpr hsum_nonneg
  have hrewrite : deltaS x = - (x.? * x.gradH + x.µ * x.Es) := by
    unfold deltaS
    ring
  simpa [hrewrite] using this

/-- If ?, µ > 0, gradH > 0, and E? > 0, then ?S < 0 (strictly).
This corresponds to the \"stabilizing quadrant\" where ?Syn pushes entropy down. -/
lemma deltaS_neg_of_pos (x : DeltaSynInput)
    (h?pos : 0 < x.?) (hµpos : 0 < x.µ)
    (hgradHpos : 0 < x.gradH) (hEspos : 0 < x.Es) :
    deltaS x < 0 := by
  unfold deltaS
  -- Consider the sum S' = ? ?H + µ E?; if each factor is positive, the sum is positive.
  have h1 : 0 < x.? * x.gradH := mul_pos h?pos hgradHpos
  have h2 : 0 < x.µ * x.Es    := mul_pos hµpos hEspos
  have hsumpos : 0 < x.? * x.gradH + x.µ * x.Es := add_pos h1 h2
  have hrewrite : deltaS x = - (x.? * x.gradH + x.µ * x.Es) := by
    unfold deltaS
    ring
  simpa [hrewrite] using neg_pos.mpr hsumpos

end Coherence
