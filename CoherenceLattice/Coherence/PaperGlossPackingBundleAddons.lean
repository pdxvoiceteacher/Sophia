import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons
import CoherenceLattice.Coherence.PaperGlossSunflowerPointAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossPackingBundleAddons

A narrative-friendly packing bundle that carries:

- indices n1, n2, N
- two bundled polar points (radius + angle + x,y + bound)
- a monotone-radius witness r(n1) <= r(n2)
- explicit unit-disk bounds for both points

Public API uses ASCII nonzero hypothesis: hN0 : (N = 0 -> False).
-/

/-- Bundle: two placements + constraints that enable “packing” narration. -/
structure SunflowerPackingBundle where
  n1 : Nat
  n2 : Nat
  N  : Nat
  p1 : SunflowerPolarPoint
  p2 : SunflowerPolarPoint
  radius_mono : p1.r <= p2.r
  bound1 : p1.x ^ 2 + p1.y ^ 2 <= 1
  bound2 : p2.x ^ 2 + p2.y ^ 2 <= 1

/-- Constructor: build the packing bundle from n1 <= n2 <= N and N != 0 (ASCII form). -/
def sunflowerPackingBundle
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) : SunflowerPackingBundle :=
  let p1 := sunflowerPolarPoint n1 N hN0 h1N
  let p2 := sunflowerPolarPoint n2 N hN0 h2N
  have hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  have hr0 : Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N :=
    Coherence.PhyllotaxisDisk.radius_mono_of_le n1 n2 N hN0' h12
  have hr : p1.r <= p2.r := by
    simpa [p1, p2, sunflowerPolarPoint] using hr0
  { n1 := n1
    n2 := n2
    N  := N
    p1 := p1
    p2 := p2
    radius_mono := hr
    bound1 := p1.bound
    bound2 := p2.bound }

/-- (Paper Lemma) Radius monotonicity contained in the bundle. -/
theorem Lemma_PackingBundleRadiusMono
    (n1 n2 N : Nat) (hN0 : N = 0 -> False) (h12 : n1 <= n2) (h1N : n1 <= N) (h2N : n2 <= N) :
    (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p1.r
      <= (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p2.r :=
  (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).radius_mono

/-- (Paper Lemma) Unit-disk bounds contained in the bundle. -/
theorem Lemma_PackingBundleBounds
    (n1 n2 N : Nat) (hN0 : N = 0 -> False) (h12 : n1 <= n2) (h1N : n1 <= N) (h2N : n2 <= N) :
    And ((sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p1.x ^ 2
          + (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p1.y ^ 2 <= 1)
        ((sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p2.x ^ 2
          + (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p2.y ^ 2 <= 1) := by
  refine And.intro ?_ ?_
  · exact (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).bound1
  · exact (sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).bound2

end
end PaperGloss
end Coherence