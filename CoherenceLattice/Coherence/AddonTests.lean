import Mathlib
import CoherenceLattice.Coherence.Basic
import CoherenceLattice.Coherence.Lattice
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.BetaRefutationAddons
import CoherenceLattice.Coherence.TotalActionFunctionalAddons
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence

noncomputable section

-- Sacred geometry sanity checks
example : Coherence.SacredGeometry.centeredHex 2 = 19 := by
  norm_num [Coherence.SacredGeometry.centeredHex]

example :
    Coherence.SacredGeometry.phi * Coherence.SacredGeometry.phi
      = Coherence.SacredGeometry.phi + 1 :=
  Coherence.SacredGeometry.phi_sq

-- Coherence lattice bounds sanity check
example (s : Coherence.Lattice.State) :
    0 ≤ Coherence.Lattice.psi s ∧ Coherence.Lattice.psi s ≤ 1 :=
  Coherence.Lattice.psi_bounds s

-- Beta refutation proposition check
example :
    ¬ ∃ b : ℝ,
        Coherence.BetaRefutation.systemHigh.M =
          Coherence.BetaRefutation.systemHigh.I ^ b ∧
        Coherence.BetaRefutation.systemLow.M =
          Coherence.BetaRefutation.systemLow.I ^ b :=
  Coherence.BetaRefutation.no_fixed_b_example

-- PaperGloss layer check (TAF unfold wrapper)
example (phi : Coherence.TAF.Phi) (x : Coherence.TAF.XSt) (a : Coherence.TAF.Agent) :
    Coherence.TAF.S_total phi x a
      = Coherence.TAF.S_theta phi + Coherence.TAF.S_info phi x + Coherence.TAF.S_coh x a := by
  simpa using Coherence.PaperGloss.Lemma_TAF_Unfold phi x a

end
end Coherence