import Mathlib

namespace Coherence

noncomputable section

/-- Mean of a nonempty list of reals. (Toy version; for pedagogy.) -/
def listMean (xs : List R) : R :=
  match xs with
  | []      => 0
  | hd :: tl =>
      let n := (hd :: tl).length
      ((hd :: tl).foldl (fun acc x => acc + x) 0) / n

/-- Toy variance: average squared deviation from mean. -/
def listVar (xs : List R) : R :=
  match xs with
  | []      => 0
  | hd :: tl =>
      let µ := listMean (hd :: tl)
      let n := (hd :: tl).length
      ((hd :: tl).foldl (fun acc x => acc + (x - µ)^2) 0) / n

/-- A toy ? index: normalized variance of the series. In real code you would integrate autocorrelation as well. -/
def lambdaIndex (xs : List R) (baseVar : R) : R :=
  if baseVar = 0 then 0 else listVar xs / baseVar

/-- Sketch: if we scale xs by a (a ? 0) and adjust baseVar by a^2, ? is invariant. (Proof left as TODO.) -/
lemma lambda_affine_invariant (xs : List R) (a b : R)
    (hbase : listVar xs ? 0) :
    lambdaIndex (xs.map (fun x => a * x + b)) (a^2 * listVar xs) = lambdaIndex xs (listVar xs) := by
  -- TODO: prove var(a x + b) = a^2 var(x), then simplify both sides.
  sorry

end Coherence
