import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `acoustics`: the speed of sound, sound levels, point sources, pipe resonances and reverberation times. After editing the article, run

    lake exe leanify prepare tests/Acoustics/article.tex --lean tests/Acoustics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `acoustics`. -/
def Acoustics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["acoustics"]

#leanify_article Acoustics "article.tex" "fnv1a64:95afa4785a415152" with Acoustics.vocabulary
