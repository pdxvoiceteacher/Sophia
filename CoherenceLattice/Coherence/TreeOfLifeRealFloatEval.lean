import Mathlib
import CoherenceLattice.Coherence.TreeOfLifeAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace TreeOfLifeRealFloatEval

/-!
# TreeOfLifeRealFloatEval

Sanity-only spot check output.

Because `Real` has no executable `Repr` and `sephiraPsi` is noncomputable,
we do:
- `#eval` rows with exact `Rat` psi + Float psi
- `#reduce` the Real term `sephiraPsi s` (prints expression, not a decimal)

This keeps everything non-proof and robust on Windows.
-/

open Coherence.TreeOfLife

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

def all : List Sephira :=
  [.keter, .chokmah, .binah, .chesed, .gevurah, .tiphereth, .netzach, .hod, .yesod, .malkuth]

-- Float psi from the synced fraction tables
def psiFloat (s : Sephira) : Float :=
  (EFrac s).toFloat * (TFrac s).toFloat

-- Exact psi as Rat derived from the same Nat fractions:
-- psi = (En/Eden) * (Tn/Tden) = (En*Tn)/(Eden*Tden)
def psiRat (s : Sephira) : Rat :=
  let e := EFrac s
  let t := TFrac s
  ((e.num * t.num : Nat) : Rat) / ((e.den * t.den : Nat) : Rat)

structure Row where
  name : String
  psiRat : Rat
  psiFloat : Float
deriving Repr

def row (s : Sephira) : Row :=
  { name := sephiraName s
    psiRat := psiRat s
    psiFloat := psiFloat s }

def rows : List Row := all.map row

#eval rows

-- Real expression spot checks (prints the term structure)
#reduce (sephiraPsi Sephira.keter)
#reduce (sephiraPsi Sephira.chokmah)
#reduce (sephiraPsi Sephira.binah)
#reduce (sephiraPsi Sephira.chesed)
#reduce (sephiraPsi Sephira.gevurah)
#reduce (sephiraPsi Sephira.tiphereth)
#reduce (sephiraPsi Sephira.netzach)
#reduce (sephiraPsi Sephira.hod)
#reduce (sephiraPsi Sephira.yesod)
#reduce (sephiraPsi Sephira.malkuth)

end TreeOfLifeRealFloatEval
end Coherence