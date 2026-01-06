import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

-- sunflowerPoint bound
example (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PaperGloss.sunflowerPoint n N hN0 hn).x ^ 2
      + (Coherence.PaperGloss.sunflowerPoint n N hN0 hn).y ^ 2 <= 1 :=
  Coherence.PaperGloss.Lemma_SunflowerPointBound n N hN0 hn

-- sunflowerPolarPoint bound
example (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).x ^ 2
      + (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).y ^ 2 <= 1 :=
  Coherence.PaperGloss.Lemma_SunflowerPolarPointBound n N hN0 hn

-- packing bundle: monotone radius fact is present
example (n1 n2 N : Nat) (hN0 : N = 0 -> False) (h12 : n1 <= n2) (h1N : n1 <= N) (h2N : n2 <= N) :
    (Coherence.PaperGloss.sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p1.r
      <= (Coherence.PaperGloss.sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p2.r :=
  Coherence.PaperGloss.Lemma_PackingBundleRadiusMono n1 n2 N hN0 h12 h1N h2N

-- packing bundle: both unit-disk bounds are present
example (n1 n2 N : Nat) (hN0 : N = 0 -> False) (h12 : n1 <= n2) (h1N : n1 <= N) (h2N : n2 <= N) :
    And ((Coherence.PaperGloss.sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p1.x ^ 2
          + (Coherence.PaperGloss.sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p1.y ^ 2 <= 1)
        ((Coherence.PaperGloss.sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p2.x ^ 2
          + (Coherence.PaperGloss.sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N).p2.y ^ 2 <= 1) :=
  Coherence.PaperGloss.Lemma_PackingBundleBounds n1 n2 N hN0 h12 h1N h2N

end
end Coherence