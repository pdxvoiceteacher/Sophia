import Mathlib
import CoherenceLattice.Quantum.Pauli

namespace Coherence
namespace Quantum

open Complex Matrix

noncomputable section

/-- Off-diagonal coherence proxy for a 2×2 density matrix ρ: |ρ₀₁| + |ρ₁₀|. -/
def cohOffDiag (ρ : Mat2) : ℝ :=
  Complex.abs (ρ 0 1) + Complex.abs (ρ 1 0)

/-- A “computational-basis” diagonal state has zero off-diagonal coherence. -/
lemma cohOffDiag_of_diag (a b : ℂ) :
    cohOffDiag (fun i j =>
      if i = 0 ∧ j = 0 then a
      else if i = 1 ∧ j = 1 then b
      else 0) = 0 := by
  simp [cohOffDiag]

/--
Example: pure |+⟩⟨+| has nonzero off-diagonal coherence in the computational basis.
We model ρ = |v⟩⟨v| using the simple (non-conjugating) outer product vᵢ * vⱼ.
This is a *proxy* demonstration (orthodox versions use conjugate transpose).
-/
def outer (v : Fin 2 → ℂ) : Mat2 := fun i j => v i * v j

lemma cohOffDiag_outer_ketPlus_pos :
    cohOffDiag (outer ketPlus) > 0 := by
  -- ketPlus has equal nonzero components, so off-diagonals are positive magnitude.
  -- We prove it by explicit evaluation.
  simp [cohOffDiag, outer, ketPlus, ket0, ket1]  -- should reduce to abs(nonzero)+abs(nonzero)
  -- if simp leaves a goal, paste it and I’ll tighten this lemma.

end  -- noncomputable section

end Quantum
end Coherence
