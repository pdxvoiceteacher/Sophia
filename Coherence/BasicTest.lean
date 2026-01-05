import Coherence.Basic

namespace Coherence

noncomputable section

/-- Examples to test coherence invariants (?) and ?Syn law. -/

-- Example: Coherence at extreme values (E = 1, T = 1 yields ? = 1)
example : psi { E := 1, T := 1, hE0 := by norm_num, hE1 := by norm_num, hT0 := by norm_num, hT1 := by norm_num } = 1 := by simp

-- Example: Coherence is zero if any component is zero (E = 0 or T = 0 yields ? = 0)
example : psi { E := 0, T := 0.5, hE0 := by norm_num, hE1 := by norm_num, hT0 := by norm_num, hT1 := by norm_num } = 0 := by
  simp [psi]
  norm_num

-- Example: ? is monotonic in E (for fixed T, increasing E increases ?)
example : psi { E := 0.4, T := 0.9, hE0 := by norm_num, hE1 := by norm_num, hT0 := by norm_num, hT1 := by norm_num } =
          psi { E := 0.7, T := 0.9, hE0 := by norm_num, hE1 := by norm_num, hT0 := by norm_num, hT1 := by norm_num } :=
  psi_mono_E 0.9 (by norm_num) 0.4 0.7 (by norm_num) (by norm_num) (by norm_num)

/-- Prepare an example ?Syn input with positive parameters. -/
def exampleDelta : DeltaSynInput := { ? := 1, µ := 1, gradH := 2, Es := 3, h?0 := by norm_num, hµ0 := by norm_num }

/-- ?S should compute to -5 for the above example (?=1, µ=1, ?H=2, E?=3). -/
example : deltaS exampleDelta = -5 := by
  simp [deltaS]
  norm_num

/-- ?S is non-positive when ?H and E? are nonnegative (here strictly positive). -/
example : deltaS exampleDelta = 0 := deltaS_nonpos_of_nonneg exampleDelta (by norm_num) (by norm_num)

/-- ?S is strictly negative when all parameters are positive. -/
example : deltaS exampleDelta < 0 := deltaS_neg_of_pos exampleDelta (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Coherence
