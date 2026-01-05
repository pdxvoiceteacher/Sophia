import Coherence.Lambda

namespace Coherence

noncomputable section

/-- Example list of reals for ?-index tests. -/
def xs : List R := [1, 2, 3]

/-- The ?-index of a series relative to its own variance should be 1. -/
example : lambdaIndex xs (listVar xs) = 1 := by
  have h : listVar xs ? 0 := by
    simp [listMean, listVar]
    norm_num
  simp [lambdaIndex, listMean, listVar, h]
  norm_num

/-- Affine invariance test: scaling by a and shifting by b leaves ? unchanged (with baseVar adjusted by a^2). -/
def ys : List R := xs.map (fun x => 2 * x + 5)

example : lambdaIndex ys (4 * listVar xs) = lambdaIndex xs (listVar xs) := by
  have h : listVar xs ? 0 := by
    simp [listMean, listVar]
    norm_num
  simp [lambdaIndex, listMean, listVar, h]
  norm_num

end Coherence
