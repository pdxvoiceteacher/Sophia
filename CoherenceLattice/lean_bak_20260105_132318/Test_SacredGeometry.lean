/-!
# Test_SacredGeometry

This test module verifies key identities and values defined in `SacredGeometry`. In particular, it checks that the golden ratio constant `φ` satisfies its defining quadratic identity.
-/
import SacredGeometry
open SacredGeometry

theorem goldenRatio_identity : φ * φ = φ + 1 := by
  have h : (Real.sqrt 5) * (Real.sqrt 5) = 5 := Real.sqrt_mul_self (by norm_num)
  calc (1 + Real.sqrt 5)^2 / 4
       = (1 + 2 * Real.sqrt 5 + (Real.sqrt 5)^2) / 4           := by ring
       ... = (1 + 2 * Real.sqrt 5 + 5) / 4                      := by rw [h]
       ... = (6 + 2 * Real.sqrt 5) / 4                          := by norm_num
       ... = (2 + (1 + Real.sqrt 5)) / 2                        := by rw [add_comm]
       ... = 2 / 2 + (1 + Real.sqrt 5) / 2                      := by rw [add_div]
       ... = 1 + (1 + Real.sqrt 5) / 2                          := by norm_num
       ... = φ + 1                                             := by rfl
