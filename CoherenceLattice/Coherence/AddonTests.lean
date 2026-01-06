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
    And (0 <= Coherence.Phyllotaxis.turnFrac n) (Coherence.Phyllotaxis.turnFrac n < 1) :=
  Coherence.PaperGloss.Lemma_TurnFracBounds n

example (n : Nat) :
    And (0 <= Coherence.Phyllotaxis.angle n) (Coherence.Phyllotaxis.angle n < (2 * Real.pi)) :=
  Coherence.PaperGloss.Lemma_AngleBounds n

example (hirr : Irrational Coherence.Phyllotaxis.goldenTurn) (n k : Nat)
    (h : Coherence.Phyllotaxis.turnFrac (n + k) = Coherence.Phyllotaxis.turnFrac n) :
    k = 0 :=
  Coherence.PaperGloss.Theorem_NoShortPeriod hirr n k h

-- New: golden angle degrees formula
example :
    Coherence.PhyllotaxisDegrees.goldenAngleDeg
      = 360 * (1 - 1 / Coherence.SacredGeometry.phi) :=
  Coherence.PaperGloss.Lemma_GoldenAngleDegrees

-- New: degree/radian consistency
example :
    Coherence.PhyllotaxisDegrees.degToRad Coherence.PhyllotaxisDegrees.goldenAngleDeg
      = Coherence.PhyllotaxisDegrees.goldenAngleRad :=
  Coherence.PaperGloss.Lemma_GoldenAngleDegToRad

end
end Coherence