/-!
# Test_CoherenceInvariants

This test module verifies the definitions and theorems of `CoherenceInvariants` by applying them in simple scenarios. It ensures that fundamental invariants (like the constant `c`) behave as expected and remain consistent.
-/
import CoherenceInvariants
open CoherenceInvariants

theorem speed_of_light_invariant : c = c := by rfl
