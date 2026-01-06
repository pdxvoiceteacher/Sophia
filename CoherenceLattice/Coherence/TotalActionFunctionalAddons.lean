import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace TAF

noncomputable section

-- Abstract state spaces
axiom Phi   : Type
axiom XSt   : Type
axiom Agent : Type

-- Component action terms
axiom S_theta : Phi -> Real
axiom S_info  : Phi -> XSt -> Real
axiom S_coh   : XSt -> Agent -> Real

-- Total action functional
def S_total (phi : Phi) (x : XSt) (a : Agent) : Real :=
  S_theta phi + S_info phi x + S_coh x a

@[simp] lemma S_total_unfold (phi : Phi) (x : XSt) (a : Agent) :
    S_total phi x a = S_theta phi + S_info phi x + S_coh x a := by
  rfl

end
end TAF
end Coherence