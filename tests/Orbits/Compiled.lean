import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `orbits`: vis-viva speeds, apsides, orbital energies, Hohmann transfers, synodic periods and Hill radii. After editing the article, run

    lake exe leanify prepare tests/Orbits/article.tex --lean tests/Orbits/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `orbits`. -/
def Orbits.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["orbits"]

#leanify_article Orbits "article.tex" "fnv1a64:53ee0422f6619371" with Orbits.vocabulary
