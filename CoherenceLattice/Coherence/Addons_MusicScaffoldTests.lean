import Mathlib
import CoherenceLattice.Coherence.MusicScaleScaffoldAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

-- applyScale produces a list of Reals
example (f : Real) :
    (Coherence.MusicScaffold.applyScale f Coherence.MusicScaffold.justScale0).length = 6 := by
  simp [Coherence.MusicScaffold.applyScale, Coherence.MusicScaffold.justScale0]

-- a simple chordOK example: [unison, P5, octave] is consonant
example :
    Coherence.MusicScaffold.chordOK
      [Coherence.MusicScaffold.unison, Coherence.MusicScaffold.P5, Coherence.MusicScaffold.octave] := by
  -- Forall reduces to membership checks
  simp [Coherence.MusicScaffold.chordOK,
        Coherence.MusicScaffold.isConsonant,
        Coherence.MusicScaffold.consonantSet,
        Coherence.MusicScaffold.unison,
        Coherence.MusicScaffold.P5,
        Coherence.MusicScaffold.octave]

end
end Coherence