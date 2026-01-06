import Mathlib
import CoherenceLattice.Coherence.TreeOfLifeAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace TreeOfLifeBandEval

/-!
# TreeOfLifeBandEval

Float-only sanity output (NOT a theorem).
Prints for each Sephira:
- name
- E,T
- psi = E*T
- band based on thresholds 0.2,0.4,0.6,0.8
-/

open Coherence.TreeOfLife

def bandF (psi : Float) : Nat :=
  if psi < 0.2 then 0
  else if psi < 0.4 then 1
  else if psi < 0.6 then 2
  else if psi < 0.8 then 3
  else 4

-- Mirror the TreeOfLifeAddons mapping as Float (so we can #eval)
def sephiraETF : Sephira -> (Float × Float)
  | .keter     => (1.0, 1.0)
  | .chokmah   => (0.9, 0.7)
  | .binah     => (0.7, 0.9)
  | .chesed    => (0.8, 0.6)
  | .gevurah   => (0.6, 0.8)
  | .tiphereth => (0.75, 0.75)
  | .netzach   => (0.6, 0.4)
  | .hod       => (0.4, 0.6)
  | .yesod     => (0.5, 0.5)
  | .malkuth   => (0.2, 0.2)

def sephiraName : Sephira -> String
  | .keter     => "keter"
  | .chokmah   => "chokmah"
  | .binah     => "binah"
  | .chesed    => "chesed"
  | .gevurah   => "gevurah"
  | .tiphereth => "tiphereth"
  | .netzach   => "netzach"
  | .hod       => "hod"
  | .yesod     => "yesod"
  | .malkuth   => "malkuth"

structure Row where
  name : String
  E : Float
  T : Float
  psi : Float
  band : Nat
deriving Repr

def row (s : Sephira) : Row :=
  let et := sephiraETF s
  let e := et.1
  let t := et.2
  let p := e * t
  { name := sephiraName s, E := e, T := t, psi := p, band := bandF p }

def all : List Sephira :=
  [.keter, .chokmah, .binah, .chesed, .gevurah, .tiphereth, .netzach, .hod, .yesod, .malkuth]

def rows : List Row := all.map row

def csvHeader : String := "name,E,T,psi,band"
def csvLine (r : Row) : String :=
  s!"{r.name},{r.E},{r.T},{r.psi},{r.band}"

def csv : String := String.intercalate "\n" (csvHeader :: rows.map csvLine)

#eval rows
#eval csv

end TreeOfLifeBandEval
end Coherence