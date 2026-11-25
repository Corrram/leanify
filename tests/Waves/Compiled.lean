import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `waves`: wavelengths, Doppler and beat frequencies, harmonics of strings, Snell's law, critical and Brewster angles, decibels and thin lenses. After editing the article, run

    lake exe leanify prepare tests/Waves/article.tex --lean tests/Waves/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `waves`. -/
def Waves.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["waves"]

#leanify_article Waves "article.tex" "fnv1a64:b4d1a25375ffe116" with Waves.vocabulary
