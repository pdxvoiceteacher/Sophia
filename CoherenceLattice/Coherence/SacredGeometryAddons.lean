import Mathlib

set_option linter.style.commandStart false

namespace Coherence
namespace SacredGeometry

noncomputable section

/-!
# SacredGeometryAddons

ASCII-safe sacred-geometry helpers for CoherenceLattice.
Greek letters can remain in prose; identifiers here are ASCII to avoid Windows encoding issues.
-/

/-- Golden ratio phi = (1 + sqrt 5) / 2. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Defining identity: phi^2 = phi + 1. -/
lemma phi_sq : phi * phi = phi + 1 := by
  unfold phi
  have hsq : (Real.sqrt (5 : ℝ)) * (Real.sqrt (5 : ℝ)) = (5 : ℝ) := by
    simpa using (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (5 : ℝ)))
  nlinarith [hsq]

/-- Fibonacci numbers: F(0)=0, F(1)=1, F(n+2)=F(n+1)+F(n). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n+2) => fib (n+1) + fib n

/-- Centered hexagonal numbers: 1,7,19,37,... -/
def centeredHex (n : Nat) : Nat := 3 * n * (n + 1) + 1

lemma centeredHex_0 : centeredHex 0 = 1 := by
  simp [centeredHex]

lemma centeredHex_1 : centeredHex 1 = 7 := by
  norm_num [centeredHex]

lemma centeredHex_2 : centeredHex 2 = 19 := by
  norm_num [centeredHex]

/-- Convenience constants. -/
def sqrt2 : ℝ := Real.sqrt 2
def sqrt3 : ℝ := Real.sqrt 3
def pi    : ℝ := Real.pi

/-- Classical consonant ratios (Pythagorean intervals). -/
def ratioOctave : ℚ := 2
def ratioFifth  : ℚ := (3 : ℚ) / 2
def ratioFourth : ℚ := (4 : ℚ) / 3
def ratioMaj3   : ℚ := (5 : ℚ) / 4

end  -- closes noncomputable section
end SacredGeometry
end Coherence