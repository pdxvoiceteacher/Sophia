/-!
# Test_BetaRefutation

This test module confirms that the `BetaRefutation` module's logic is sound. It uses the proven result from `BetaRefutation` to show that assuming `Beta` leads to a contradiction (`False`), thereby validating that Beta is refuted in the coherence lattice theory.
-/
import BetaRefutation
open BetaRefutation

theorem Beta_contradiction : ¬ Beta := by
  intro H
  exact beta_false H
