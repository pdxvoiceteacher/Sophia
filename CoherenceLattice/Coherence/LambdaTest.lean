import Coherence.Lambda
import Mathlib.Tactic.NormNum

noncomputable section
open Coherence

example : listMean [1, 2, 3] = 2 := by norm_num

example : listVar [1, 3] = 1 := by
  simp [listVar, listMean]
  norm_num

example : lambdaIndex [1, 3] (listVar [1, 3]) = 1 := by
  simp [lambdaIndex, listVar, listMean]
  norm_num

example : lambdaIndex [1, 1, 1] (listVar [1, 1, 1]) = 0 := by
  simp [lambdaIndex, listVar, listMean]
  norm_num
