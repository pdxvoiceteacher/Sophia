import CoherenceLattice.Coherence.TotalActionFunctionalAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace TAF

noncomputable section

example (phi : Phi) (x : XSt) (a : Agent) :
    S_total phi x a = S_theta phi + S_info phi x + S_coh x a := by
  simp [S_total]

end
end TAF
end Coherence