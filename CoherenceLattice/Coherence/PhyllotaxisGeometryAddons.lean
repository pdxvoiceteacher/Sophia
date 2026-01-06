import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PhyllotaxisGeometry

noncomputable section

open Coherence.Phyllotaxis

/-- 2D point on the unit circle derived from phyllotaxis angle. -/
def point (n : Nat) : Real × Real :=
  (Real.cos (angle n), Real.sin (angle n))

/-- x-coordinate of point n. -/
def px (n : Nat) : Real := (point n).1

/-- y-coordinate of point n. -/
def py (n : Nat) : Real := (point n).2

/-- The point lies on the unit circle: cos^2 + sin^2 = 1. -/
lemma point_on_unit_circle (n : Nat) :
    (px n) ^ 2 + (py n) ^ 2 = 1 := by
  unfold px py point
  -- standard identity: cos^2 + sin^2 = 1
  simpa [pow_two] using (Real.cos_sq_add_sin_sq (angle n))

/-- Both coordinates are bounded by [-1,1]. -/
lemma point_coord_bounds (n : Nat) :
    (-1 ≤ px n ∧ px n ≤ 1) ∧ (-1 ≤ py n ∧ py n ≤ 1) := by
  constructor
  · -- bounds for cos
    unfold px point
    exact ⟨Real.neg_one_le_cos (angle n), Real.cos_le_one (angle n)⟩
  · -- bounds for sin
    unfold py point
    exact ⟨Real.neg_one_le_sin (angle n), Real.sin_le_one (angle n)⟩

end
end PhyllotaxisGeometry
end Coherence