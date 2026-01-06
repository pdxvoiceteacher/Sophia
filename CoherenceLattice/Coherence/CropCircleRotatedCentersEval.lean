import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace CropCircleRotatedCentersEval

/-!
# CropCircleRotatedCentersEval

Float-only CSV output demonstrating rotation invariance of distance-from-origin, with:

- per-angle summary row (i=-1) reporting:
  maxAbsDiff, maxAbsDiffToR, okAngle
- per-angle comment separators starting with "#"
- okAngle field filled on data rows as empty-string "" (strict CSV-friendly)
- global summary row at end with theta=-1, i=-1:
  maxAbsDiffAll, maxAbsDiffToRAll, okAll

CSV columns:
theta,i,cx,cy,cxRot,cyRot,rBase,rRot,absDiff,absDiffToR,okAngle
-/

def piF : Float := 3.141592653589793
def eps : Float := 0.000001

def absF (x : Float) : Float := if x < 0.0 then -x else x
def maxF (a b : Float) : Float := if a < b then b else a

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
  "theta,i,cx,cy,cxRot,cyRot,rBase,rRot,absDiff,absDiffToR,okAngle"

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

  let mut first : Bool := true
  let mut maxAbsDiffAll : Float := 0.0
  let mut maxAbsDiffToRAll : Float := 0.0

  for th in angles do
    if first then
      first := false
    else
      IO.println "# ---- next angle ----"

    let mut maxAbsDiff : Float := 0.0
    let mut maxAbsDiffToR : Float := 0.0

    for row in base do
      let iNat := row.1
      let cx := row.2.1
      let cy := row.2.2
      let p2 := rotPointF th (cx, cy)
      let cx2 := p2.1
      let cy2 := p2.2
      let rBase := normF cx cy
      let rRot  := normF cx2 cy2
      let absDiff := absF (rRot - rBase)
      let absDiffToR := absF (rRot - RF0)

      maxAbsDiff := maxF maxAbsDiff absDiff
      maxAbsDiffToR := maxF maxAbsDiffToR absDiffToR

      -- Fill okAngle field explicitly as empty string "" for strict CSV parsers.
      IO.println s!"{th},{(Int.ofNat iNat)},{cx},{cy},{cx2},{cy2},{rBase},{rRot},{absDiff},{absDiffToR},\"\""

    let okAngle : Bool := (maxAbsDiff < eps) && (maxAbsDiffToR < eps)

    -- Per-angle summary row (i=-1), aligned to columns (cx..rRot blank)
    IO.println s!"{th},-1,,,,,,{maxAbsDiff},{maxAbsDiffToR},{okAngle}"

    -- Update global maxima
    maxAbsDiffAll := maxF maxAbsDiffAll maxAbsDiff
    maxAbsDiffToRAll := maxF maxAbsDiffToRAll maxAbsDiffToR

  let okAll : Bool := (maxAbsDiffAll < eps) && (maxAbsDiffToRAll < eps)
  IO.println "# ---- global summary ----"
  IO.println s!"{-1.0},-1,,,,,,{maxAbsDiffAll},{maxAbsDiffToRAll},{okAll}"

#eval emit

end CropCircleRotatedCentersEval
end Coherence