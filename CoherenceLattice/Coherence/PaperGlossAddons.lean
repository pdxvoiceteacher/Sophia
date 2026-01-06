import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons
import CoherenceLattice.Coherence.PaperGlossSunflowerPointAddons
import CoherenceLattice.Coherence.PaperGlossPackingBundleAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons (surface)

We keep everything ASCII-safe in public signatures:
- hN0 : (N = 0 -> False)
- <= for ordering
- And for conjunction

Bridge lemma provides two implications (corollary -> bundle-facts) and (bundle-facts -> corollary).
-/

/-- Inequality/corollary statement (Prop). -/
def CorollaryProp3 (n1 n2 N : Nat) : Prop :=
  And (Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N)
      (And ((Coherence.PhyllotaxisDisk.px n1 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n1 N) ^ 2 <= 1)
           ((Coherence.PhyllotaxisDisk.px n2 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n2 N) ^ 2 <= 1))

/-- Bundle-extracted statement (Prop). -/
def BundleFacts3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) : Prop :=
  let b := sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N
  And (b.p1.r <= b.p2.r)
      (And (b.p1.x ^ 2 + b.p1.y ^ 2 <= 1)
           (b.p2.x ^ 2 + b.p2.y ^ 2 <= 1))

/-- Proof of the inequality/corollary statement. -/
theorem Corollary_SunflowerPacking3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) :
    CorollaryProp3 n1 n2 N := by
  have hN0' : Ne N 0 := by
    intro h
    exact hN0 h
  refine And.intro (Coherence.PhyllotaxisDisk.radius_mono_of_le n1 n2 N hN0' h12) ?_
  refine And.intro
    (Coherence.PhyllotaxisDisk.normSq_le_one_of_le n1 N hN0' h1N)
    (Coherence.PhyllotaxisDisk.normSq_le_one_of_le n2 N hN0' h2N)

/-- Prop: inequality form implies bundle form. -/
def CorollaryToBundle3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) : Prop :=
  CorollaryProp3 n1 n2 N -> BundleFacts3 n1 n2 N hN0 h12 h1N h2N

/-- Prop: bundle form implies inequality form. -/
def BundleToCorollary3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) : Prop :=
  BundleFacts3 n1 n2 N hN0 h12 h1N h2N -> CorollaryProp3 n1 n2 N

/-- Bridge: both implications in one And. -/
theorem Lemma_BundleEquivCorollary3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) :
    And (CorollaryToBundle3 n1 n2 N hN0 h12 h1N h2N)
        (BundleToCorollary3 n1 n2 N hN0 h12 h1N h2N) := by
  refine And.intro ?_ ?_
  · intro _hc
    -- Goal is BundleFacts3 ... ; do not unfold CorollaryToBundle3 here.
    -- Use the bundle lemmas and simp with a local abbreviation.
    let b := sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N
    have hr0 :=
      Lemma_PackingBundleRadiusMono n1 n2 N hN0 h12 h1N h2N
    have hb0 :=
      Lemma_PackingBundleBounds n1 n2 N hN0 h12 h1N h2N
    -- Reduce the goal to And (b.p1.r <= b.p2.r) (And ...)
    -- by unfolding BundleFacts3 and rewriting the internal let to our local b.
    simp [BundleFacts3, b]
    refine And.intro ?_ ?_
    · simpa [b] using hr0
    · simpa [b] using hb0
  · intro _hb
    -- Goal is CorollaryProp3 ... ; no need to unfold BundleToCorollary3 here.
    exact Corollary_SunflowerPacking3 n1 n2 N hN0 h12 h1N h2N

end
end PaperGloss
end Coherence