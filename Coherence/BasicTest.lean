import Coherence.Basic
import Coherence.Regime
import Mathlib.Tactic.NormNum

noncomputable section
open Coherence

/-- Define a sample CoherenceInput with E=0.5, T=0.8 (within [0,1]). -/
noncomputable def testCI : CoherenceInput := {
  E   := 0.5,
  T   := 0.8,
  hE0 := by norm_num,  -- 0 = 0.5
  hE1 := by norm_num,  -- 0.5 = 1
  hT0 := by norm_num,  -- 0 = 0.8
  hT1 := by norm_num   -- 0.8 = 1
}

/-- Define a sample DeltaSynInput with positive ?, µ, gradH, Es. -/
noncomputable def exDelta : DeltaSynInput := {
  ?   := 2,
  µ   := 1,
  gradH := 3,
  Es    := 4,
  h?0 := by norm_num,   -- 0 = 2
  hµ0 := by norm_num    -- 0 = 1
}

/-- Evaluate the adjacency list of the terminal regime state (s4). -/
#eval adj Regime.s4
-- Expected output: [s0, s4] (allowed transitions from s4)

-- Coherence ? for testCI should equal E*T = 0.4.
example : psi testCI = 0.4 := by norm_num

-- ? is always between 0 and 1 for valid inputs.
theorem psi_range (x : CoherenceInput) : 0 = psi x ? psi x = 1 :=
  ?psi_nonneg x, psi_le_one x?

-- ?S is non-positive when gradH, Es = 0 (given ?, µ = 0).
example : deltaS exDelta = 0 :=
  deltaS_nonpos_of_nonneg exDelta (by norm_num) (by norm_num)

-- ?S is strictly negative when ?, µ, gradH, Es are all > 0.
example : deltaS exDelta < 0 :=
  deltaS_neg_of_pos exDelta (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Adjacency function correctness: Regime.s0 transitions to [s0, s1].
example : adj Regime.s0 = [Regime.s0, Regime.s1] := rfl

-- Example path validity: s0 ? s1 ? s2 is a valid transition path.
example : validPath [Regime.s0, Regime.s1, Regime.s2] := by
  simp [validPath, adj]
end
