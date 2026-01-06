import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence

noncomputable section

example (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PaperGloss.sunflowerPoint n N hN0 hn).x ^ 2
      + (Coherence.PaperGloss.sunflowerPoint n N hN0 hn).y ^ 2 <= 1 :=
  Coherence.PaperGloss.Lemma_SunflowerPointBound n N hN0 hn

example (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).x ^ 2
      + (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).y ^ 2 <= 1 :=
  Coherence.PaperGloss.Lemma_SunflowerPolarPointBound n N hN0 hn

example (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).x
      = (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).r
          * Real.cos ((Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).theta)
    ∧
    (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).y
      = (Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).r
          * Real.sin ((Coherence.PaperGloss.sunflowerPolarPoint n N hN0 hn).theta) :=
  Coherence.PaperGloss.Lemma_SunflowerPolarPointXY n N hN0 hn

end
end Coherence