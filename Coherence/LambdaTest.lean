import Coherence.Lambda
import Mathlib.Tactic.NormNum

noncomputable section
open Coherence

-- The mean of [1, 2, 3] should be 2.
example : listMean [1, 2, 3] = 2 := by norm_num

-- The variance of [1, 3] is 1 (since the mean is 2 and deviations are ±1).
example : listVar [1, 3] = 1 := by
  simp [listVar, listMean]
  norm_num

-- If baseVar is the variance of the list, lambdaIndex returns 1.
example : lambdaIndex [1, 3] (listVar [1, 3]) = 1 := by
  simp [lambdaIndex, listVar, listMean]
  norm_num

-- If the variance is zero (all elements equal), lambdaIndex returns 0 regardless of baseVar.
example : lambdaIndex [1, 1, 1] (listVar [1, 1, 1]) = 0 := by
  simp [lambdaIndex, listVar, listMean]
  norm_num
end
