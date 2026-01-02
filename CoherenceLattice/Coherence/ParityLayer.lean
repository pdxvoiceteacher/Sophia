import Mathlib

namespace Coherence
namespace Parity

noncomputable section

/-- Forward parity layer: C = φ (Q + A). -/
def forward (φ q a : ℝ) : ℝ := φ * (q + a)

/-- Reverse reconstruction: Q̂ = C/φ - A. -/
def reverse (φ c a : ℝ) : ℝ := c / φ - a

/-- Drift metric: |Q - Q̂|. -/
def drift (φ q a : ℝ) : ℝ := abs (q - reverse φ (forward φ q a) a)

/-- Exact parity: reverse(forward(q)) = q if φ ≠ 0. -/
lemma parity_inverse {φ q a : ℝ} (hφ : φ ≠ 0) :
    reverse φ (forward φ q a) a = q := by
  unfold reverse forward
  -- simp cancels (φ * (q+a)) / φ using hφ
  field_simp [hφ]
  ring

/-- Therefore drift = 0 (ideal arithmetic). -/
lemma drift_zero {φ q a : ℝ} (hφ : φ ≠ 0) :
    drift φ q a = 0 := by
  unfold drift
  simp [parity_inverse hφ]

end  -- noncomputable section

end Parity
end Coherence
