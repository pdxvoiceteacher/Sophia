import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.BetaRefutationAddons
import CoherenceLattice.Coherence.TotalActionFunctionalAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons

Paper-facing lemma names for manuscript citation.
No new theory: this file re-exports stable theorem names that wrap internal lemmas.
-/

/-- (Paper Lemma) Golden ratio identity: phi^2 = phi + 1. -/
theorem Lemma_PhiSquared :
    Coherence.SacredGeometry.phi * Coherence.SacredGeometry.phi
      = Coherence.SacredGeometry.phi + 1 :=
  Coherence.SacredGeometry.phi_sq

/-- (Paper Lemma) Centered hex number at n=2 is 19 (Flower-of-Life ring count sanity). -/
theorem Lemma_CenteredHex_2 :
    Coherence.SacredGeometry.centeredHex 2 = 19 := by
  simpa using Coherence.SacredGeometry.centeredHex_2

/-- (Paper Theorem) No fixed exponent b satisfies M = I^b for both example systems. -/
theorem Theorem_NoFixedExponentExample :
    ¬ ∃ b : ℝ,
        Coherence.BetaRefutation.systemHigh.M =
          Coherence.BetaRefutation.systemHigh.I ^ b ∧
        Coherence.BetaRefutation.systemLow.M =
          Coherence.BetaRefutation.systemLow.I ^ b :=
  Coherence.BetaRefutation.no_fixed_b_example

/-- (Paper Lemma) Total Action Functional unfolds into its component sum. -/
theorem Lemma_TAF_Unfold
    (phi : Coherence.TAF.Phi) (x : Coherence.TAF.XSt) (a : Coherence.TAF.Agent) :
    Coherence.TAF.S_total phi x a
      = Coherence.TAF.S_theta phi + Coherence.TAF.S_info phi x + Coherence.TAF.S_coh x a := by
  simpa using Coherence.TAF.S_total_unfold phi x a

end
end PaperGloss
end Coherence