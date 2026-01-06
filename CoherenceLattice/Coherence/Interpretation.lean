import CoherenceLattice.Coherence.DynamicsET

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.unusedSimpArgs false
noncomputable section

/-- Paper interpretation: negative ΔS implies positive "drive". -/
lemma drive_pos_of_deltaS_neg (p : Coherence.DeltaSynInput)
    (h : Coherence.deltaS p < 0) : 0 < drive p := by
  unfold drive
  linarith

/-- If δ ≥ 0 then the capped increment capDeltaET δ is also ≥ 0. -/
lemma capDeltaET_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ capDeltaET δ := by
  unfold capDeltaET
  have ha : 0 ≤ tau0 / 4 := by unfold tau0; norm_num
  have hmin : 0 ≤ min δ (tau0 / 4) := le_min hδ ha
  exact le_trans hmin (le_max_right _ _)

/-- If x ∈ [0,1] and c ≥ 0, then clamping (x+c) to [0,1] does not decrease x. -/
lemma le_clamp01Real_add {x c : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hc : 0 ≤ c) :
    x ≤ clamp01Real (x + c) := by
  by_cases h : x + c ≤ 1
  · have h0 : 0 ≤ x + c := add_nonneg hx0 hc
    have hmin : min (x + c) 1 = x + c := min_eq_left h
    have hmax : max 0 (x + c) = x + c := max_eq_right h0
    have hxle : x ≤ x + c := le_add_of_nonneg_right hc
    simpa [clamp01Real, hmin, hmax] using hxle
  · have hge : 1 ≤ x + c := le_of_not_ge h
    have hmin : min (x + c) 1 = (1 : ℝ) := min_eq_right hge
    -- clamp01Real (x+c) = 1, and x ≤ 1
    simpa [clamp01Real, hmin] using hx1

/-- E is nondecreasing under stepET if the E-increment is ≥ 0. -/
lemma E_le_stepET (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : State)
    (hcE : 0 ≤ capDeltaET (deltaE ηE p)) :
    E s ≤ E (stepET ηE ηT p s) := by
  have hx :
      E s ≤ clamp01Real (E s + capDeltaET (deltaE ηE p)) :=
    le_clamp01Real_add (x := E s) (c := capDeltaET (deltaE ηE p))
      (E_nonneg s) (E_le_one s) hcE
  simpa [stepET, E] using hx

/-- T is nondecreasing under stepET if the T-increment is ≥ 0. -/
lemma T_le_stepET (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : State)
    (hcT : 0 ≤ capDeltaET (deltaT ηT p)) :
    T s ≤ T (stepET ηE ηT p s) := by
  have hx :
      T s ≤ clamp01Real (T s + capDeltaET (deltaT ηT p)) :=
    le_clamp01Real_add (x := T s) (c := capDeltaET (deltaT ηT p))
      (T_nonneg s) (T_le_one s) hcT
  simpa [stepET, T] using hx

/-- If E and T both increase (componentwise), then Ψ = E*T increases. -/
lemma psi_mono_of_E_T {s₁ s₂ : State}
    (hE : E s₁ ≤ E s₂) (hT : T s₁ ≤ T s₂) :
    psi s₁ ≤ psi s₂ := by
  unfold psi
  have h1 : E s₁ * T s₁ ≤ E s₂ * T s₁ :=
    mul_le_mul_of_nonneg_right hE (T_nonneg s₁)
  have h2 : E s₂ * T s₁ ≤ E s₂ * T s₂ :=
    mul_le_mul_of_nonneg_left hT (E_nonneg s₂)
  exact le_trans h1 h2

/--
Paper-friendly interpretation lemma:
If ΔS < 0 (so drive > 0) and ηE, ηT ≥ 0, then stepET cannot decrease Ψ.
-/
theorem psi_stepET_nondec_of_deltaS_neg
    (ηE ηT : ℝ) (hηE : 0 ≤ ηE) (hηT : 0 ≤ ηT)
    (p : Coherence.DeltaSynInput) (hΔS : Coherence.deltaS p < 0) (s : State) :
    psi s ≤ psi (stepET ηE ηT p s) := by
  have hdrive : 0 < drive p := drive_pos_of_deltaS_neg p hΔS
  have hδE : 0 ≤ deltaE ηE p := by
    unfold deltaE
    exact mul_nonneg hηE (le_of_lt hdrive)
  have hδT : 0 ≤ deltaT ηT p := by
    unfold deltaT
    exact mul_nonneg hηT (le_of_lt hdrive)
  have hcE : 0 ≤ capDeltaET (deltaE ηE p) := capDeltaET_nonneg hδE
  have hcT : 0 ≤ capDeltaET (deltaT ηT p) := capDeltaET_nonneg hδT
  have hE : E s ≤ E (stepET ηE ηT p s) := E_le_stepET ηE ηT p s hcE
  have hT : T s ≤ T (stepET ηE ηT p s) := T_le_stepET ηE ηT p s hcT
  exact psi_mono_of_E_T hE hT

/--
Bounded drift lemma (deterministic): regardless of sign,
|ΔΨ| ≤ τ₀/2 per stepET.
This is the formal backbone for any “in expectation” narrative:
any averaging over runs cannot exceed this per-step bound.
-/
theorem abs_psi_stepET_sub_le (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : State) :
    |psi (stepET ηE ηT p s) - psi s| ≤ (tau0 / 2) := by
  -- Bound |ΔE| ≤ tau0/4
  have hE :
      |E (stepET ηE ηT p s) - E s| ≤ (tau0 / 4) := by
    have h1 :
        |E (stepET ηE ηT p s) - E s|
          ≤ |capDeltaET (deltaE ηE p)| := by
      have := abs_clamp01Real_add_sub_le_abs
        (x := E s) (c := capDeltaET (deltaE ηE p))
        (E_nonneg s) (E_le_one s)
      simpa [stepET, E] using this
    exact le_trans h1 (abs_capDeltaET_le (deltaE ηE p))
  -- Bound |ΔT| ≤ tau0/4
  have hT :
      |T (stepET ηE ηT p s) - T s| ≤ (tau0 / 4) := by
    have h1 :
        |T (stepET ηE ηT p s) - T s|
          ≤ |capDeltaET (deltaT ηT p)| := by
      have := abs_clamp01Real_add_sub_le_abs
        (x := T s) (c := capDeltaET (deltaT ηT p))
        (T_nonneg s) (T_le_one s)
      simpa [stepET, T] using this
    exact le_trans h1 (abs_capDeltaET_le (deltaT ηT p))
  -- Lipschitz bound: |ΔΨ| ≤ |ΔE| + |ΔT|
  have hpsi_le :
      |psi (stepET ηE ηT p s) - psi s|
        ≤ |E (stepET ηE ηT p s) - E s| + |T (stepET ηE ηT p s) - T s| :=
    abs_psi_sub_le_abs_dE_add_abs_dT s (stepET ηE ηT p s)
  have hsum :
      |E (stepET ηE ηT p s) - E s| + |T (stepET ηE ηT p s) - T s| ≤ (tau0 / 2) := by
    have : |E (stepET ηE ηT p s) - E s| + |T (stepET ηE ηT p s) - T s|
            ≤ (tau0 / 4) + (tau0 / 4) := add_le_add hE hT
    have ht : (tau0 / 4) + (tau0 / 4) = (tau0 / 2) := by unfold tau0; norm_num
    simpa [ht] using this
  exact le_trans hpsi_le hsum

end

end Lattice
end Coherence
