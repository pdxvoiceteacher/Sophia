import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons (clean)

This file is a paper-facing surface. It intentionally uses ASCII-only relational syntax:
- not-zero is expressed as (N = 0 -> False)
- ordering uses <=
This avoids Windows encoding drift that can introduce stray characters like `â`.
-/

/-- (Paper Corollary) Monotone spiral radius + both points in unit disk (3 facts). -/
theorem Corollary_SunflowerPacking3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) :
    And (Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N)
        (And ((Coherence.PhyllotaxisDisk.px n1 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n1 N) ^ 2 <= 1)
             ((Coherence.PhyllotaxisDisk.px n2 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n2 N) ^ 2 <= 1)) := by
  -- Convert ASCII not-zero to the disk lemma’s N ≠ 0 requirement (internally, safe here).
  have hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  exact Coherence.PhyllotaxisDisk.sunflower_packing_corollary3 n1 n2 N hN0' h12 h1N h2N

end
end PaperGloss
end Coherence