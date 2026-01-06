import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDegreesAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PhyllotaxisDegreesEval

/-!
# PhyllotaxisDegreesEval

Numerical sanity check (NOT a theorem):
Compute approximations of the golden angle:
  - degrees: 360 * (1 - 1/phi) ≈ 137.507...
  - radians: (pi/180) * degrees ≈ 2.39996...

We use Float so it does not affect proof stability.
-/

-- Float approximation of phi
def phiF : Float := 1.618033988749895

-- Derived golden angle in degrees
def goldenAngleDegF : Float :=
  360.0 * (1.0 - (1.0 / phiF))

-- Float approximation of pi
def piF : Float := 3.141592653589793

-- Degrees to radians conversion for Float
def degToRadF (deg : Float) : Float :=
  deg * piF / 180.0

-- Golden angle in radians (converted from degrees)
def goldenAngleRadF : Float :=
  degToRadF goldenAngleDegF

#eval goldenAngleDegF
#eval goldenAngleRadF

end PhyllotaxisDegreesEval
end Coherence