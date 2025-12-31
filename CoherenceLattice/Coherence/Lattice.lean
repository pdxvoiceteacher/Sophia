import Mathlib

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false

/-- Unit interval [0,1] as a subtype of ℝ. -/
abbrev Unit01 := {x : ℝ // 0 ≤ x ∧ x ≤ 1}

instance : CoeTC Unit01 ℝ := ⟨fun x => x.1⟩
instance : LE Unit01 := ⟨fun a b => (a : ℝ) ≤ (b : ℝ)⟩

/-- A coherence state is a point (E,T) in the unit square. -/
abbrev State := Unit01 × Unit01

def E (s : State) : ℝ := s.1
def T (s : State) : ℝ := s.2

/-- Coherence Ψ = E * T. -/
def psi (s : State) : ℝ := E s * T s

lemma E_nonneg (s : State) : 0 ≤ E s := s.1.2.1
lemma E_le_one (s : State) : E s ≤ 1 := s.1.2.2
lemma T_nonneg (s : State) : 0 ≤ T s := s.2.2.1
lemma T_le_one (s : State) : T s ≤ 1 := s.2.2.2

lemma psi_nonneg (s : State) : 0 ≤ psi s := by
  unfold psi E T
  exact mul_nonneg (E_nonneg s) (T_nonneg s)

lemma psi_le_one (s : State) : psi s ≤ 1 := by
  unfold psi E T
  have hET_le_E : (E s) * (T s) ≤ (E s) := by
    exact mul_le_of_le_one_right (E_nonneg s) (T_le_one s)
  exact le_trans hET_le_E (E_le_one s)

lemma psi_bounds (s : State) : 0 ≤ psi s ∧ psi s ≤ 1 :=
  ⟨psi_nonneg s, psi_le_one s⟩

/-- Monotonicity of Ψ w.r.t. componentwise order on State. -/
lemma psi_mono {s₁ s₂ : State} (h : s₁ ≤ s₂) : psi s₁ ≤ psi s₂ := by
  rcases h with ⟨hE, hT⟩
  unfold psi E T
  have h1 : (E s₁) * (T s₁) ≤ (E s₂) * (T s₁) :=
    mul_le_mul_of_nonneg_right hE (T_nonneg s₁)
  have h2 : (E s₂) * (T s₁) ≤ (E s₂) * (T s₂) :=
    mul_le_mul_of_nonneg_left hT (E_nonneg s₂)
  exact le_trans h1 h2

end Lattice
end Coherence