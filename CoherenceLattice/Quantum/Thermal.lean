import Mathlib
import CoherenceLattice.Quantum.Pauli

namespace Coherence
namespace Quantum

open Complex Matrix

noncomputable section

/-- Two-level Hamiltonian H = (Δ/2) σz. -/
def H (Δ : ℂ) : Mat2 := (Δ / 2) • σz

/-- Explicit diagonal exp(-βH) for H=(Δ/2)σz. -/
def expNegβH (β Δ : ℂ) : Mat2 := fun i j =>
  if i = 0 ∧ j = 0 then Complex.exp (-(β * Δ / 2))
  else if i = 1 ∧ j = 1 then Complex.exp ( (β * Δ / 2))
  else 0

/-- Trace for 2×2 matrices: tr(A)=A00 + A11. -/
def tr2 (A : Mat2) : ℂ := A 0 0 + A 1 1

/-- Partition function Z(β)=tr(exp(-βH)). -/
def Z (β Δ : ℂ) : ℂ := tr2 (expNegβH β Δ)

/-- Closed form Z(β)=exp(-βΔ/2)+exp(+βΔ/2). -/
lemma Z_closed (β Δ : ℂ) :
    Z β Δ = Complex.exp (-(β * Δ / 2)) + Complex.exp (β * Δ / 2) := by
  simp [Z, tr2, expNegβH]

/-- Gibbs state ρβ := exp(-βH) / Z(β). -/
def ρ (β Δ : ℂ) : Mat2 := (1 / Z β Δ) • expNegβH β Δ

/-- tr(ρβ)=1, assuming Z≠0. -/
lemma trace_rho (β Δ : ℂ) (hZ : Z β Δ ≠ 0) :
    tr2 (ρ β Δ) = 1 := by
  have h : tr2 (ρ β Δ) = (1 / Z β Δ) * Z β Δ := by
    simp [ρ, Z, tr2, expNegβH, mul_add]
  simpa [h] using (one_div_mul_cancel hZ)

end  -- closes noncomputable section

end Quantum
end Coherence
