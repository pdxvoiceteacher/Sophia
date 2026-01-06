import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossSunflowerPointAddons

A narrative-friendly constructor that returns a sunflower point (x,y) together with
a proof that it lies in the unit disk (x^2 + y^2 <= 1).

This is intentionally lightweight: it reuses the proven disk bound from PhyllotaxisDiskAddons.
-/

/-- A sunflower point bundled with its unit-disk bound. -/
structure SunflowerPoint where
  x : Real
  y : Real
  bound : x ^ 2 + y ^ 2 <= 1

/--
Constructor: produce the sunflower point at index n for total N, along with its bound.

We use ASCII for not-equal assumption: hN0 : (N = 0 -> False).
-/
def sunflowerPoint (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) : SunflowerPoint :=
  let hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  { x := Coherence.PhyllotaxisDisk.px n N
    y := Coherence.PhyllotaxisDisk.py n N
    bound := by
      simpa using Coherence.PhyllotaxisDisk.normSq_le_one_of_le n N hN0' hn }

/-- (Paper Lemma) The bundled constructor’s bound, as a stable citation hook. -/
theorem Lemma_SunflowerPointBound (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (sunflowerPoint n N hN0 hn).x ^ 2 + (sunflowerPoint n N hN0 hn).y ^ 2 <= 1 :=
  (sunflowerPoint n N hN0 hn).bound

end
end PaperGloss
end Coherence