import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossSunflowerPointAddons

Narrative-friendly bundled constructors:

1) sunflowerPoint: returns (x,y) + proof it lies in the unit disk.
2) sunflowerPolarPoint: returns (r, theta, x, y) + proof it lies in the unit disk.

We use ASCII for nonzero assumptions: hN0 : (N = 0 -> False).
-/

-- -------------------------
-- (A) Point-only bundle
-- -------------------------

structure SunflowerPoint where
  x : Real
  y : Real
  bound : x ^ 2 + y ^ 2 <= 1

def sunflowerPoint (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) : SunflowerPoint :=
  let hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  { x := Coherence.PhyllotaxisDisk.px n N
    y := Coherence.PhyllotaxisDisk.py n N
    bound := by
      simpa using Coherence.PhyllotaxisDisk.normSq_le_one_of_le n N hN0' hn }

theorem Lemma_SunflowerPointBound (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (sunflowerPoint n N hN0 hn).x ^ 2 + (sunflowerPoint n N hN0 hn).y ^ 2 <= 1 :=
  (sunflowerPoint n N hN0 hn).bound

-- -------------------------
-- (B) Polar + point bundle
-- -------------------------

structure SunflowerPolarPoint where
  r : Real
  theta : Real
  x : Real
  y : Real
  bound : x ^ 2 + y ^ 2 <= 1

def sunflowerPolarPoint (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) : SunflowerPolarPoint :=
  let hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  { r := Coherence.PhyllotaxisDisk.radius n N
    theta := Coherence.PhyllotaxisDisk.theta n
    x := Coherence.PhyllotaxisDisk.px n N
    y := Coherence.PhyllotaxisDisk.py n N
    bound := by
      simpa using Coherence.PhyllotaxisDisk.normSq_le_one_of_le n N hN0' hn }

theorem Lemma_SunflowerPolarPointBound (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (sunflowerPolarPoint n N hN0 hn).x ^ 2 + (sunflowerPolarPoint n N hN0 hn).y ^ 2 <= 1 :=
  (sunflowerPolarPoint n N hN0 hn).bound

theorem Lemma_SunflowerPolarPointXY (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (sunflowerPolarPoint n N hN0 hn).x
      = (sunflowerPolarPoint n N hN0 hn).r
          * Real.cos ((sunflowerPolarPoint n N hN0 hn).theta)
    ∧
    (sunflowerPolarPoint n N hN0 hn).y
      = (sunflowerPolarPoint n N hN0 hn).r
          * Real.sin ((sunflowerPolarPoint n N hN0 hn).theta) := by
  constructor
  · simp [sunflowerPolarPoint, Coherence.PhyllotaxisDisk.px]
  · simp [sunflowerPolarPoint, Coherence.PhyllotaxisDisk.py]

end
end PaperGloss
end Coherence