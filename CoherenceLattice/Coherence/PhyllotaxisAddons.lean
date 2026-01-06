import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace Phyllotaxis

noncomputable section

open Coherence.SacredGeometry

/-- Fractional part via floor: frac(x) = x - floor(x).  -/
def frac (x : Real) : Real := x - (Int.floor x : Real)

/-- frac(x) is always nonnegative. -/
lemma frac_nonneg (x : Real) : 0 ≤ frac x := by
  unfold frac
  -- Int.floor x ≤ x  => 0 ≤ x - floor x
  exact sub_nonneg.mpr (Int.floor_le x)

/-- frac(x) is always < 1. -/
lemma frac_lt_one (x : Real) : frac x < 1 := by
  unfold frac
  -- x < floor x + 1  => x - floor x < 1
  have hx : x < (Int.floor x : Real) + 1 := Int.lt_floor_add_one x
  -- use: a - b < c ↔ a < c + b
  have hx' : x < 1 + (Int.floor x : Real) := by simpa [add_comm, add_left_comm, add_assoc] using hx
  exact (sub_lt_iff_lt_add).2 hx'

/-- Golden turn fraction: 1 - 1/phi. -/
def goldenTurn : Real := 1 - 1 / phi

/-- Turn fraction for step n, wrapped into [0,1) using frac. -/
def turnFrac (n : Nat) : Real := frac ((n : Real) * goldenTurn)

/-- turnFrac is always in [0,1). -/
lemma turnFrac_bounds (n : Nat) : 0 ≤ turnFrac n ∧ turnFrac n < 1 := by
  unfold turnFrac
  exact And.intro (frac_nonneg ((n : Real) * goldenTurn)) (frac_lt_one ((n : Real) * goldenTurn))

/-- Angle position in radians for step n, wrapped into [0,2*pi). -/
def angle (n : Nat) : Real := (2 * Real.pi) * turnFrac n

/-- angle is always in [0, 2*pi). -/
lemma angle_bounds (n : Nat) : 0 ≤ angle n ∧ angle n < (2 * Real.pi) := by
  have hb : 0 ≤ turnFrac n ∧ turnFrac n < 1 := turnFrac_bounds n
  have hpos : 0 < (2 * Real.pi) := by nlinarith [Real.pi_pos]
  constructor
  · exact mul_nonneg (le_of_lt hpos) hb.1
  ·
    have hlt : (2 * Real.pi) * turnFrac n < (2 * Real.pi) * (1 : Real) :=
      mul_lt_mul_of_pos_left hb.2 hpos
    simpa [angle] using hlt

end
end Phyllotaxis
end Coherence