import Mathlib

namespace Coherence

inductive Regime
  | s0 | s1 | s2 | s3 | s4
deriving DecidableEq, Repr

open Regime

/-- Symmetric “ring + neighbors” adjacency. -/
def adj : Regime → List Regime
  | s0 => [s4, s0, s1]
  | s1 => [s0, s1, s2]
  | s2 => [s1, s2, s3]
  | s3 => [s2, s3, s4]
  | s4 => [s3, s4, s0]

def validPath : List Regime → Prop
  | [] => True
  | [_] => True
  | r1 :: r2 :: tl => (r2 ∈ adj r1) ∧ validPath (r2 :: tl)

example : validPath [s0, s1, s2] := by
  simp [validPath, adj]

end Coherence