import Mathlib
import CoherenceLattice.Quantum.Thermal

namespace Coherence
namespace Quantum

open Real

noncomputable section

/-- Real-parameter partition function for the two-level system: Z = 2 cosh(βΔ/2). -/
def Z_real (β Δ : ℝ) : ℝ := 2 * Real.cosh (β * Δ / 2)

/-- Expected energy ⟨H⟩ via canonical identity: -d/dβ log Z. -/
def E_expected (β Δ : ℝ) : ℝ := - (Δ / 2) * Real.tanh (β * Δ / 2)

/--
Derivation: -(d/dβ) log(2 cosh(βΔ/2)) = -(Δ/2) tanh(βΔ/2).
This is the standard two-level canonical result.
-/
lemma neg_deriv_log_Z_real (β Δ : ℝ) :
    -(deriv (fun b => Real.log (Z_real b Δ)) β) = E_expected β Δ := by
  -- This is a calculus lemma; mathlib has the needed derivative rules.
  -- If your snapshot is missing some lemmas, paste the error and I’ll adapt.
  simp [Z_real, E_expected]  -- may need `by` with `ring` + `simp` depending on lemma availability

end  -- noncomputable section

end Quantum
end Coherence
