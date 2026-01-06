import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PhyllotaxisNoPeriod

noncomputable section

/-!
# PhyllotaxisNoPeriodAddons

Guardrail axiom (Stage 1):
If the step size goldenTurn is irrational, then the wrapped turn sequence has no nontrivial period.

This is accepted as an axiom for now to avoid mathlib-lemma drift;
it can be upgraded to a full proof later.
-/

/-- If goldenTurn is irrational, then turnFrac (n+k) = turnFrac n implies k = 0. -/
axiom no_short_period
    (hirr : Irrational Coherence.Phyllotaxis.goldenTurn)
    (n k : Nat)
    (h : Coherence.Phyllotaxis.turnFrac (n + k) = Coherence.Phyllotaxis.turnFrac n) :
    k = 0

end
end PhyllotaxisNoPeriod
end Coherence