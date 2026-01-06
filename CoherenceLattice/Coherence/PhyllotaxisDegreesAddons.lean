import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.PhyllotaxisAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PhyllotaxisDegrees

noncomputable section

open Coherence.SacredGeometry
open Coherence.Phyllotaxis

/-- Degrees to radians: deg * pi / 180. -/
def degToRad (deg : Real) : Real := deg * Real.pi / 180

/-- Radians to degrees: rad * 180 / pi. -/
def radToDeg (rad : Real) : Real := rad * 180 / Real.pi

/-- Golden angle in degrees: 360 * (1 - 1/phi). -/
def goldenAngleDeg : Real := 360 * Coherence.Phyllotaxis.goldenTurn

/-- Golden angle in radians: (2*pi) * (1 - 1/phi). -/
def goldenAngleRad : Real := (2 * Real.pi) * Coherence.Phyllotaxis.goldenTurn

/-- Golden-angle formula in degrees: 360 * (1 - 1/phi). -/
lemma goldenAngleDeg_formula :
    goldenAngleDeg = 360 * (1 - 1 / Coherence.SacredGeometry.phi) := by
  simp [goldenAngleDeg, Coherence.Phyllotaxis.goldenTurn]

/-- Degree/radian consistency for the golden angle:
degToRad(360*(1-1/phi)) = (2*pi)*(1-1/phi). -/
lemma degToRad_goldenAngle :
    degToRad goldenAngleDeg = goldenAngleRad := by
  have h180 : (180 : Real) != 0 := by norm_num
  unfold degToRad goldenAngleDeg goldenAngleRad
  -- Clear the /180 and finish by ring arithmetic
  field_simp [h180]
  ring

end
end PhyllotaxisDegrees
end Coherence