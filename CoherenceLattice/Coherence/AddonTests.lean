import Mathlib
import CoherenceLattice.Coherence.Basic
import CoherenceLattice.Coherence.Lattice
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.BetaRefutationAddons

set_option linter.style.commandStart false

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

-- Beta refutation: state the proposition as the type, use the theorem as proof
example :
    ¬ ∃ b : ℝ,
        Coherence.BetaRefutation.systemHigh.M =
          Coherence.BetaRefutation.systemHigh.I ^ b ∧
        Coherence.BetaRefutation.systemLow.M =
          Coherence.BetaRefutation.systemLow.I ^ b :=
  Coherence.BetaRefutation.no_fixed_b_example

end  -- closes noncomputable section
end Coherence