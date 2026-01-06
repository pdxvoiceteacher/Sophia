import Mathlib
import CoherenceLattice.Coherence.CropCirclesAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace CropCirclesEval

/-!
# CropCirclesEval

Float-only style CSV output (NOT a theorem; intended for Python diffing).

We print a rosette ring:
- centers (cx, cy) for k circles
- fixed radii rRing
- plus a center circle rCenter

This is "bells & whistles" output only and does not affect proof modules.
-/

open Coherence.CropCircles

-- Float approximations for readability
def piF : Float := 3.141592653589793

def angleStepF (k : Nat) : Float :=
  (2.0 * piF) / (Float.ofNat k)

def cosF (x : Float) : Float := Float.cos x
def sinF (x : Float) : Float := Float.sin x

def rosetteCentersF (k : Nat) (RF : Float) : List (Nat × Float × Float) :=
  (List.range k).map (fun i =>
    let th := (Float.ofNat i) * (angleStepF k)
    (i, RF * cosF th, RF * sinF th))

def csvHeader1 : String := "i,cx,cy"
def csvLine1 (row : Nat × Float × Float) : String :=
  s!"{row.1},{row.2.1},{row.2.2}"

def csv1 (k : Nat) (RF : Float) : String :=
  let rows := rosetteCentersF k RF
  String.intercalate "\n" (csvHeader1 :: (rows.map csvLine1))

-- Extended CSV including per-circle radius
def csvHeader2 : String := "i,cx,cy,r"
def csvLine2 (rRing : Float) (row : Nat × Float × Float) : String :=
  s!"{row.1},{row.2.1},{row.2.2},{rRing}"

def csv2 (k : Nat) (RF rRing : Float) : String :=
  let rows := rosetteCentersF k RF
  String.intercalate "\n" (csvHeader2 :: (rows.map (csvLine2 rRing)))

-- Parameters (edit freely)
def k0 : Nat := 12
def RF0 : Float := 1.0
def rCenter0 : Float := 0.3
def rRing0 : Float := 0.2

#eval (k0, RF0, rCenter0, rRing0)
#eval csv1 k0 RF0
#eval csv2 k0 RF0 rRing0

end CropCirclesEval
end Coherence