import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace CropCircleRotationInvarianceEval

/-!
# CropCircleRotationInvarianceEval

Float-only "rotation invariance" signature sanity check.

We define a simple signature:
  order = k
  count = k+1
  totalArea = pi*rCenter^2 + k*pi*rRing^2

Rotation by any angle preserves all three by construction.
We still print several angles (0, 2pi/k, pi/k, pi/7, pi/3) to provide
a repeatable validation artifact for Python comparison.
-/

def piF : Float := 3.141592653589793

def areaF (r : Float) : Float := piF * (r*r)

def totalAreaF (k : Nat) (rCenter rRing : Float) : Float :=
  areaF rCenter + (Float.ofNat k) * areaF rRing

structure Sig where
  order : Nat
  count : Nat
  totalArea : Float
deriving Repr

def sig (k : Nat) (rCenter rRing : Float) : Sig :=
  { order := k
    count := k + 1
    totalArea := totalAreaF k rCenter rRing }

-- "Rotate": geometrically would rotate circle centers, but signature ignores positions.
def rotateSig (theta : Float) (s : Sig) : Sig := s

def sigEq (a b : Sig) : Bool :=
  decide (a.order = b.order) && decide (a.count = b.count) && (a.totalArea == b.totalArea)

def csvHeader : String := "theta,order,count,totalArea,okSame"
def line (theta : Float) (s0 sT : Sig) : String :=
  let ok := sigEq s0 sT
  s!"{theta},{sT.order},{sT.count},{sT.totalArea},{ok}"

def emit : IO Unit := do
  let k0 : Nat := 12
  let rC : Float := 0.3
  let rR : Float := 0.2
  let s0 := sig k0 rC rR

  let angles : List Float :=
    [0.0,
     (2.0*piF) / (Float.ofNat k0),
     piF / (Float.ofNat k0),
     piF / 7.0,
     piF / 3.0]

  IO.println csvHeader
  for th in angles do
    let sT := rotateSig th s0
    IO.println (line th s0 sT)

#eval emit

end CropCircleRotationInvarianceEval
end Coherence