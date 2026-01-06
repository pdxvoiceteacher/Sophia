import Mathlib
import CoherenceLattice.Coherence.MusicRatioAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace MusicScaffold

noncomputable section

/-!
# MusicScaleScaffoldAddons

Lean-light scaffolding for generative music work:

- Scale := List Real
- applyScale : multiply base frequency by ratios
- basic "just" scale (subset)
- consonance whitelist (stub)
- chordOK predicate (stub)

No heavy audio or temperament claims; this is a utility layer.
-/

abbrev Ratio : Type := Real
abbrev Scale : Type := List Ratio

def applyRatio (f : Real) (r : Ratio) : Real := f * r

def applyScale (f : Real) (s : Scale) : List Real :=
  s.map (fun r => applyRatio f r)

-- Pull in canonical ratios from MusicRatioAddons
def unison : Ratio := Coherence.MusicRatio.ratioUnison
def m3 : Ratio := Coherence.MusicRatio.ratioMinorThird
def M3 : Ratio := Coherence.MusicRatio.ratioMajorThird
def P4 : Ratio := Coherence.MusicRatio.ratioFourth
def P5 : Ratio := Coherence.MusicRatio.ratioFifth
def octave : Ratio := Coherence.MusicRatio.ratioOctave

/-- A minimal "just" scale scaffold (editable later). -/
def justScale0 : Scale := [unison, m3, M3, P4, P5, octave]

/-- Consonance whitelist stub (expand later). -/
def consonantSet : Scale := [unison, M3, P4, P5, octave]

def isConsonant (r : Ratio) : Prop := r ∈ consonantSet

/-- Chord is OK if all ratios are in consonantSet (stub; can become graded later). -/
def chordOK (rs : List Ratio) : Prop :=
  List.Forall isConsonant rs

-- Small helper lemma: unison is consonant (by construction)
lemma unison_consonant : isConsonant unison := by
  simp [isConsonant, consonantSet, unison]

end
end MusicScaffold
end Coherence