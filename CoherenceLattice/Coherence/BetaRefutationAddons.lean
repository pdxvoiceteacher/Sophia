import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace BetaRefutation

noncomputable section

/-!
# BetaRefutationAddons

Minimal, ASCII-safe refutation:

If two systems share the same information value I but have different masses,
no single exponent b can satisfy M = I^b for both.
-/

structure ExampleSystem where
  psi : ℝ
  M   : ℝ
  I   : ℝ

def systemHigh : ExampleSystem := { psi := 1, M := 2, I := 2 }
def systemLow  : ExampleSystem := { psi := 0, M := 4, I := 2 }

theorem no_fixed_b_example :
    ¬ ∃ b : ℝ,
        systemHigh.M = systemHigh.I ^ b ∧
        systemLow.M  = systemLow.I  ^ b := by
  intro hex
  rcases hex with ⟨b, h1, h2⟩
  have h1' : (2 : ℝ) = (2 : ℝ) ^ b := by
    simpa [systemHigh] using h1
  have h2' : (4 : ℝ) = (2 : ℝ) ^ b := by
    simpa [systemLow] using h2
  have hb  : (2 : ℝ) ^ b = 2 := h1'.symm
  have hb2 : (2 : ℝ) ^ b = 4 := h2'.symm
  have h24 : (2 : ℝ) = 4 := Eq.trans hb.symm hb2
  have hne : (2 : ℝ) ≠ 4 := by norm_num
  exact hne h24

end  -- closes noncomputable section
end BetaRefutation
end Coherence