import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

example (n1 n2 N : Nat) (hN0 : N = 0 -> False)
    (h12 : n1 <= n2) (h1N : n1 <= N) (h2N : n2 <= N) :
    And (Coherence.PaperGloss.CorollaryToBundle3 n1 n2 N hN0 h12 h1N h2N)
        (Coherence.PaperGloss.BundleToCorollary3 n1 n2 N hN0 h12 h1N h2N) :=
  Coherence.PaperGloss.Lemma_BundleEquivCorollary3 n1 n2 N hN0 h12 h1N h2N

end
end Coherence