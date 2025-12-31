import CoherenceLattice.Coherence.Trajectory

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
noncomputable section

/-- ΔSyn "drive" (positive when ΔS is negative). -/
def drive (p : Coherence.DeltaSynInput) : ℝ := -Coherence.deltaS p

def deltaE (ηE : ℝ) (p : Coherence.DeltaSynInput) : ℝ := ηE * drive p
def deltaT (ηT : ℝ) (p : Coherence.DeltaSynInput) : ℝ := ηT * drive p

/-- Cap any update to ±(tau0/4) so |ΔE| + |ΔT| ≤ tau0/2. -/
def capDeltaET (δ : ℝ) : ℝ :=
  max (-(tau0 / 4)) (min δ (tau0 / 4))

lemma capDeltaET_le (δ : ℝ) : capDeltaET δ ≤ (tau0 / 4) := by
  unfold capDeltaET
  refine (max_le_iff).2 ?_
  constructor
  · have hpos : 0 ≤ tau0 / 4 := by unfold tau0; norm_num
    linarith
  · exact min_le_right _ _

lemma neg_capDeltaET_le (δ : ℝ) : -(tau0 / 4) ≤ capDeltaET δ := by
  unfold capDeltaET
  exact le_max_left _ _

lemma abs_capDeltaET_le (δ : ℝ) : |capDeltaET δ| ≤ (tau0 / 4) := by
  apply abs_le.2
  constructor
  · exact neg_capDeltaET_le δ
  · exact capDeltaET_le δ

/-- Step that updates E and T directly, clamping each to [0,1]. -/
def stepET (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : State) : State :=
  let cE := capDeltaET (deltaE ηE p)
  let cT := capDeltaET (deltaT ηT p)
  let e2 := clamp01Real (E s + cE)
  let t2 := clamp01Real (T s + cT)
  have he0 : 0 ≤ e2 := (clamp01Real_bounds (E s + cE)).1
  have he1 : e2 ≤ 1 := (clamp01Real_bounds (E s + cE)).2
  have ht0 : 0 ≤ t2 := (clamp01Real_bounds (T s + cT)).1
  have ht1 : t2 ≤ 1 := (clamp01Real_bounds (T s + cT)).2
  (⟨e2, ⟨he0, he1⟩⟩, ⟨t2, ⟨ht0, ht1⟩⟩)

/-- Helpful bound: |E s| ≤ 1 for any state. -/
lemma abs_E_le_one (s : State) : |E s| ≤ 1 := by
  have h0 : 0 ≤ E s := E_nonneg s
  have h1 : E s ≤ 1 := E_le_one s
  simpa [abs_of_nonneg h0] using h1

/-- Helpful bound: |T s| ≤ 1 for any state. -/
lemma abs_T_le_one (s : State) : |T s| ≤ 1 := by
  have h0 : 0 ≤ T s := T_nonneg s
  have h1 : T s ≤ 1 := T_le_one s
  simpa [abs_of_nonneg h0] using h1

/--
Lipschitz-style inequality on Ψ in the unit square:
|E2*T2 - E1*T1| ≤ |E2 - E1| + |T2 - T1|.
-/
lemma abs_psi_sub_le_abs_dE_add_abs_dT (s₁ s₂ : State) :
    |psi s₂ - psi s₁| ≤ |E s₂ - E s₁| + |T s₂ - T s₁| := by
  have hdecomp :
      (E s₂) * (T s₂) - (E s₁) * (T s₁)
        = (E s₂ - E s₁) * (T s₂) + (E s₁) * (T s₂ - T s₁) := by
    ring
  have ht2 : |T s₂| ≤ 1 := abs_T_le_one s₂
  have he1 : |E s₁| ≤ 1 := abs_E_le_one s₁
  calc
    |psi s₂ - psi s₁|
        = |(E s₂) * (T s₂) - (E s₁) * (T s₁)| := by simp [psi]
    _ = |(E s₂ - E s₁) * (T s₂) + (E s₁) * (T s₂ - T s₁)| := by
          simpa [hdecomp]
    _ ≤ |(E s₂ - E s₁) * (T s₂)| + |(E s₁) * (T s₂ - T s₁)| := by
          -- triangle inequality via norm_add_le, then rewrite norms to abs
          have hnorm :
              ‖(E s₂ - E s₁) * (T s₂) + (E s₁) * (T s₂ - T s₁)‖
                ≤ ‖(E s₂ - E s₁) * (T s₂)‖ + ‖(E s₁) * (T s₂ - T s₁)‖ := by
            simpa using
              (norm_add_le
                ((E s₂ - E s₁) * (T s₂))
                ((E s₁) * (T s₂ - T s₁)))
          simpa [Real.norm_eq_abs] using hnorm
    _ = |E s₂ - E s₁| * |T s₂| + |E s₁| * |T s₂ - T s₁| := by
          simp [abs_mul]
    _ ≤ |E s₂ - E s₁| + |T s₂ - T s₁| := by
          have hA : |E s₂ - E s₁| * |T s₂| ≤ |E s₂ - E s₁| := by
            have := mul_le_mul_of_nonneg_left ht2 (abs_nonneg (E s₂ - E s₁))
            simpa using this
          have hB : |E s₁| * |T s₂ - T s₁| ≤ |T s₂ - T s₁| := by
            have := mul_le_mul_of_nonneg_right he1 (abs_nonneg (T s₂ - T s₁))
            simpa using this
          exact add_le_add hA hB

/--
Main theorem: the E/T step is always a valid regime transition,
because it forces |ΔE|,|ΔT| ≤ tau0/4 and thus |ΔΨ| < tau0.
-/
theorem validTransition_stepET (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) (s : State) :
    validTransition s (stepET ηE ηT p s) := by
  have hE :
      |E (stepET ηE ηT p s) - E s| ≤ |capDeltaET (deltaE ηE p)| := by
    have := abs_clamp01Real_add_sub_le_abs
      (x := E s) (c := capDeltaET (deltaE ηE p))
      (E_nonneg s) (E_le_one s)
    simpa [stepET, E, T] using this
  have hT :
      |T (stepET ηE ηT p s) - T s| ≤ |capDeltaET (deltaT ηT p)| := by
    have := abs_clamp01Real_add_sub_le_abs
      (x := T s) (c := capDeltaET (deltaT ηT p))
      (T_nonneg s) (T_le_one s)
    simpa [stepET, E, T] using this
  have hEc : |capDeltaET (deltaE ηE p)| ≤ (tau0 / 4) := abs_capDeltaET_le (deltaE ηE p)
  have hTc : |capDeltaET (deltaT ηT p)| ≤ (tau0 / 4) := abs_capDeltaET_le (deltaT ηT p)
  have hE' : |E (stepET ηE ηT p s) - E s| ≤ (tau0 / 4) := le_trans hE hEc
  have hT' : |T (stepET ηE ηT p s) - T s| ≤ (tau0 / 4) := le_trans hT hTc
  have hsum :
      |E (stepET ηE ηT p s) - E s| + |T (stepET ηE ηT p s) - T s| ≤ (tau0 / 2) := by
    have : |E (stepET ηE ηT p s) - E s| + |T (stepET ηE ηT p s) - T s|
            ≤ (tau0 / 4) + (tau0 / 4) := add_le_add hE' hT'
    have ht : (tau0 / 4) + (tau0 / 4) = (tau0 / 2) := by unfold tau0; norm_num
    simpa [ht] using this
  have hpsi_le :
      |psi (stepET ηE ηT p s) - psi s|
        ≤ |E (stepET ηE ηT p s) - E s| + |T (stepET ηE ηT p s) - T s| :=
    abs_psi_sub_le_abs_dE_add_abs_dT s (stepET ηE ηT p s)
  have hpsi : |psi (stepET ηE ηT p s) - psi s| ≤ (tau0 / 2) :=
    le_trans hpsi_le hsum
  have ht : (tau0 / 2) < tau0 := by unfold tau0; norm_num
  have habs : |psi (stepET ηE ηT p s) - psi s| < tau0 :=
    lt_of_le_of_lt hpsi ht
  exact validTransition_of_abs_lt_tau0 (s₁ := s) (s₂ := stepET ηE ηT p s) habs

/-- Optional: iterate stepET and get a guaranteed valid regime path. -/
def trajET (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) : Nat → State → List State :=
  traj (stepET ηE ηT p)

theorem validPath_trajET (ηE ηT : ℝ) (p : Coherence.DeltaSynInput) :
    ∀ n s, Coherence.validPath (regimePath (trajET ηE ηT p n s)) := by
  intro n s
  apply validPath_regimePath_traj (f := stepET ηE ηT p)
  intro s0
  simpa using validTransition_stepET ηE ηT p s0

end

end Lattice
end Coherence