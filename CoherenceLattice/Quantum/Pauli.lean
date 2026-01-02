import Mathlib

namespace Coherence
namespace Quantum

open Complex Matrix

noncomputable section

/-- 2×2 complex matrices. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli σx (entrywise). -/
def σx : Mat2 := fun i j =>
  if i = 0 ∧ j = 1 then (1 : ℂ)
  else if i = 1 ∧ j = 0 then (1 : ℂ)
  else 0

/-- Pauli σy. -/
def σy : Mat2 := fun i j =>
  if i = 0 ∧ j = 1 then (-Complex.I)
  else if i = 1 ∧ j = 0 then (Complex.I)
  else 0

/-- Pauli σz. -/
def σz : Mat2 := fun i j =>
  if i = 0 ∧ j = 0 then (1 : ℂ)
  else if i = 1 ∧ j = 1 then (-1 : ℂ)
  else 0

/-- Commutator: [A,B] := AB − BA. -/
def comm (A B : Mat2) : Mat2 := A * B - B * A

@[simp] lemma I_pow_two : (Complex.I : ℂ) ^ 2 = (-1 : ℂ) := by
  simp [pow_two]

/-- [σx, σy] = 2 i σz. -/
lemma comm_sigmaX_sigmaY : comm σx σy = ((2 : ℂ) * Complex.I) • σz := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, σx, σy, σz, Matrix.mul_apply] <;> ring_nf <;> simp

/-- [σy, σz] = 2 i σx. -/
lemma comm_sigmaY_sigmaZ : comm σy σz = ((2 : ℂ) * Complex.I) • σx := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, σx, σy, σz, Matrix.mul_apply] <;> ring_nf <;> simp

/-- [σz, σx] = 2 i σy. -/
lemma comm_sigmaZ_sigmaX : comm σz σx = ((2 : ℂ) * Complex.I) • σy := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, σx, σy, σz, Matrix.mul_apply] <;> ring_nf <;> simp

/-! Basis eigenstates for σz (explicit). -/

/-- |0⟩ basis vector. -/
def ket0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

/-- |1⟩ basis vector. -/
def ket1 : Fin 2 → ℂ := fun i => if i = 1 then 1 else 0

/-- Matrix–vector multiply specialized to Fin 2 (no Finset sums). -/
def mulVec (A : Mat2) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => A i 0 * v 0 + A i 1 * v 1

/-- σz |0⟩ = + |0⟩. -/
lemma σz_mul_ket0 : mulVec σz ket0 = ket0 := by
  ext i <;> fin_cases i <;> simp [mulVec, σz, ket0]

/-- σz |1⟩ = - |1⟩. -/
lemma σz_mul_ket1 : mulVec σz ket1 = (-1 : ℂ) • ket1 := by
  ext i <;> fin_cases i <;> simp [mulVec, σz, ket1]

/-- Simple dot product ⟨v,w⟩ = v0*w0 + v1*w1 (sufficient for basis normalization demo). -/
def inner (v w : Fin 2 → ℂ) : ℂ := v 0 * w 0 + v 1 * w 1
def normSq (v : Fin 2 → ℂ) : ℂ := inner v v

lemma norm_ket0 : normSq ket0 = 1 := by
  simp [normSq, inner, ket0]

lemma norm_ket1 : normSq ket1 = 1 := by
  simp [normSq, inner, ket1]

lemma orth_ket0_ket1 : inner ket0 ket1 = 0 := by
  simp [inner, ket0, ket1]

/-! σx eigenstates |±⟩ with stable √2 handling. -/

/-- inv(√2) as a complex scalar (stable across mathlib snapshots). -/
def invSqrt2 : ℂ := ((Real.sqrt (2 : ℝ)) : ℂ)⁻¹

/-- |+⟩ = (|0⟩ + |1⟩)/√2. -/
def ketPlus : Fin 2 → ℂ := fun i => invSqrt2 * (ket0 i + ket1 i)

/-- |-⟩ = (|0⟩ - |1⟩)/√2. -/
def ketMinus : Fin 2 → ℂ := fun i => invSqrt2 * (ket0 i - ket1 i)

/-- σx |+⟩ = + |+⟩. -/
lemma σx_mul_ketPlus : mulVec σx ketPlus = ketPlus := by
  ext i <;> fin_cases i <;>
    simp [mulVec, σx, ketPlus, ket0, ket1, invSqrt2] <;> ring_nf

/-- σx |-⟩ = - |-⟩. -/
lemma σx_mul_ketMinus : mulVec σx ketMinus = (-1 : ℂ) • ketMinus := by
  ext i <;> fin_cases i <;>
    simp [mulVec, σx, ketMinus, ket0, ket1, invSqrt2] <;> ring_nf

/-- Helper: (inv√2)^2 * 2 = 1. -/
lemma invSqrt2_sq_mul_two : (invSqrt2 * invSqrt2) * (2 : ℂ) = 1 := by
  have hsR : (Real.sqrt (2 : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt (2 : ℝ) := by
      simpa using Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    exact ne_of_gt hpos
  have hs : ((Real.sqrt (2 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hsR

  have hsqR : (Real.sqrt (2 : ℝ)) * (Real.sqrt (2 : ℝ)) = (2 : ℝ) := by
    simpa using (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hsq : ((Real.sqrt (2 : ℝ)) : ℂ) * ((Real.sqrt (2 : ℝ)) : ℂ) = (2 : ℂ) := by
    exact_mod_cast hsqR

  calc
    (invSqrt2 * invSqrt2) * (2 : ℂ)
        = (invSqrt2 * invSqrt2) * (((Real.sqrt (2 : ℝ)) : ℂ) * ((Real.sqrt (2 : ℝ)) : ℂ)) := by
            simpa [hsq]
    _ = 1 := by
            simp [invSqrt2, mul_assoc, mul_left_comm, mul_comm, hs]

lemma norm_ketPlus : normSq ketPlus = 1 := by
  -- reduces to invSqrt2*invSqrt2 + invSqrt2*invSqrt2
  simp [normSq, inner, ketPlus, ket0, ket1]
  -- rewrite a+a as a*2 and use the helper lemma
  have hsum :
      invSqrt2 * invSqrt2 + invSqrt2 * invSqrt2
        = (invSqrt2 * invSqrt2) * (2 : ℂ) := by
    simpa [mul_two] using (mul_two (invSqrt2 * invSqrt2)).symm
  calc
    invSqrt2 * invSqrt2 + invSqrt2 * invSqrt2
        = (invSqrt2 * invSqrt2) * (2 : ℂ) := hsum
    _ = 1 := invSqrt2_sq_mul_two

lemma norm_ketMinus : normSq ketMinus = 1 := by
  simp [normSq, inner, ketMinus, ket0, ket1]
  have hsum :
      invSqrt2 * invSqrt2 + invSqrt2 * invSqrt2
        = (invSqrt2 * invSqrt2) * (2 : ℂ) := by
    simpa [mul_two] using (mul_two (invSqrt2 * invSqrt2)).symm
  calc
    invSqrt2 * invSqrt2 + invSqrt2 * invSqrt2
        = (invSqrt2 * invSqrt2) * (2 : ℂ) := hsum
    _ = 1 := invSqrt2_sq_mul_two

lemma orth_ketPlus_ketMinus : inner ketPlus ketMinus = 0 := by
  simp [inner, ketPlus, ketMinus, ket0, ket1, invSqrt2] <;> ring_nf

end  -- closes noncomputable section

end Quantum
end Coherence
