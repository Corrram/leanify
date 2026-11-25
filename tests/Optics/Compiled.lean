import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `optics`: the lensmaker's equation, image distances, magnification, the Rayleigh angle, gratings, single slits, Bragg reflection and Malus's law. After editing the article, run

    lake exe leanify prepare tests/Optics/article.tex --lean tests/Optics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `optics`. -/
def Optics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["optics"]

#leanify_article Optics "article.tex" "fnv1a64:caef4dd6602a6fec" with Optics.vocabulary
