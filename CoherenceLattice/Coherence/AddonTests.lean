import Mathlib
import CoherenceLattice.Coherence.Basic
import CoherenceLattice.Coherence.Lattice
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.SacredGeometryLemmasAddons
import CoherenceLattice.Coherence.PhyllotaxisAddons
import CoherenceLattice.Coherence.BetaRefutationAddons
import CoherenceLattice.Coherence.TotalActionFunctionalAddons
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence

noncomputable section

-- PaperGloss checks (these guarantee the manuscript-facing layer stays green)
example (n : Nat) :
    Coherence.SacredGeometry.centeredHex (n + 1)
      = Coherence.SacredGeometry.centeredHex n + 6 * (n + 1) :=
  Coherence.PaperGloss.Lemma_CenteredHex_Succ n

example (n : Nat) :
    0 ≤ Coherence.Phyllotaxis.turnFrac n ∧ Coherence.Phyllotaxis.turnFrac n < 1 :=
  Coherence.PaperGloss.Lemma_TurnFracBounds n

example (n : Nat) :
    0 ≤ Coherence.Phyllotaxis.angle n ∧ Coherence.Phyllotaxis.angle n < (2 * Real.pi) :=
  Coherence.PaperGloss.Lemma_AngleBounds n

example :
    Coherence.SacredGeometry.ratioFourth < Coherence.SacredGeometry.ratioFifth :=
  Coherence.PaperGloss.Lemma_RatioFourth_lt_RatioFifth

example :
    Coherence.SacredGeometry.ratioFifth < Coherence.SacredGeometry.ratioOctave :=
  Coherence.PaperGloss.Lemma_RatioFifth_lt_RatioOctave

end
end Coherence