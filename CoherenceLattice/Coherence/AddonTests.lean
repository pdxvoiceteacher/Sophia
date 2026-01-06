import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence

noncomputable section

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

example (n : Nat) :
    (Coherence.PhyllotaxisGeometry.px n) ^ 2 + (Coherence.PhyllotaxisGeometry.py n) ^ 2 = 1 :=
  Coherence.PaperGloss.Lemma_PointOnUnitCircle n

example :
    Coherence.SacredGeometry.ratioFourth < Coherence.SacredGeometry.ratioFifth :=
  Coherence.PaperGloss.Lemma_RatioFourth_lt_RatioFifth

example :
    Coherence.SacredGeometry.ratioFifth < Coherence.SacredGeometry.ratioOctave :=
  Coherence.PaperGloss.Lemma_RatioFifth_lt_RatioOctave

example (phi : Coherence.TAF.Phi) (x : Coherence.TAF.XSt) (a : Coherence.TAF.Agent) :
    Coherence.TAF.S_total phi x a
      = Coherence.TAF.S_theta phi + Coherence.TAF.S_info phi x + Coherence.TAF.S_coh x a := by
  simpa using Coherence.PaperGloss.Lemma_TAF_Unfold phi x a

end
end Coherence