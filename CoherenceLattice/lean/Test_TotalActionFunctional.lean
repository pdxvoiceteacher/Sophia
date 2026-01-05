/-!
# Test_TotalActionFunctional

This test module ensures that the definitions in `TotalActionFunctional` produce expected results. We verify the total action functional on simple numeric inputs to confirm that it calculates the anticipated values.
-/
import TotalActionFunctional
open TotalActionFunctional

theorem totalAction_basic : totalAction 1 1 1 5 = 5 := by norm_num
