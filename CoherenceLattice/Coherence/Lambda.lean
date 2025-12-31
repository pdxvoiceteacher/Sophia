import Mathlib

set_option linter.style.commandStart false
noncomputable section

namespace Coherence

def listMean (xs : List ℝ) : ℝ :=
  match xs with
  | [] => 0
  | _  => xs.foldl (· + ·) 0 / (xs.length : ℝ)

def listVar (xs : List ℝ) : ℝ :=
  match xs with
  | [] => 0
  | _  =>
    let μ := listMean xs
    xs.foldl (fun acc x => acc + (x - μ)^2) 0 / (xs.length : ℝ)

/-- Toy Λ: variance normalized by a baseline variance. -/
def lambdaIndex (xs : List ℝ) (baseVar : ℝ) : ℝ :=
  if baseVar = 0 then 0 else listVar xs / baseVar

end Coherence