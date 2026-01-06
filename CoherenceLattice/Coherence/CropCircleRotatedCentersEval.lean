import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace CropCircleRotatedCentersEval

/-!
# CropCircleRotatedCentersEval

Float-only CSV output that demonstrates rotation invariance of distance-from-origin.

Columns:
theta,i,cx,cy,cxRot,cyRot,rBase,rRot,absDiff,absDiffToR

- rBase = sqrt(cx^2+cy^2)
- rRot  = sqrt(cxRot^2+cyRot^2)
- absDiff = |rRot - rBase|
- absDiffToR = |rRot - R|
-/

def piF : Float := 3.141592653589793

def absF (x : Float) : Float := if x < 0.0 then -x else x

def rotPointF (theta : Float) (p : Float × Float) : Float × Float :=
  (p.1 * Float.cos theta - p.2 * Float.sin theta,
   p.1 * Float.sin theta + p.2 * Float.cos theta)

def angleStepF (k : Nat) : Float :=
  (2.0 * piF) / (Float.ofNat k)

def rosetteCentersF (k : Nat) (RF : Float) : List (Nat × Float × Float) :=
  (List.range k).map (fun i =>
    let th := (Float.ofNat i) * (angleStepF k)
    (i, RF * Float.cos th, RF * Float.sin th))

def normF (x y : Float) : Float := Float.sqrt (x*x + y*y)

def csvHeader : String :=
  "theta,i,cx,cy,cxRot,cyRot,rBase,rRot,absDiff,absDiffToR"

def emit : IO Unit := do
  let k0 : Nat := 12
  let RF0 : Float := 1.0

  let angles : List Float :=
    [0.0,
     (2.0*piF) / (Float.ofNat k0),
     piF / (Float.ofNat k0),
     piF / 7.0,
     piF / 3.0]

  let base := rosetteCentersF k0 RF0

  IO.println csvHeader

  for th in angles do
    for row in base do
      let i  := row.1
      let cx := row.2.1
      let cy := row.2.2
      let p2 := rotPointF th (cx, cy)
      let cx2 := p2.1
      let cy2 := p2.2
      let rBase := normF cx cy
      let rRot  := normF cx2 cy2
      let absDiff := absF (rRot - rBase)
      let absDiffToR := absF (rRot - RF0)
      IO.println s!"{th},{i},{cx},{cy},{cx2},{cy2},{rBase},{rRot},{absDiff},{absDiffToR}"

#eval emit

end CropCircleRotatedCentersEval
end Coherence