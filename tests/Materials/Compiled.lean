import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `materials`: stress, strain, stiffness, elastic moduli, second moments of area, beam deflections and buckling loads. After editing the article, run

    lake exe leanify prepare tests/Materials/article.tex --lean tests/Materials/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `materials`. -/
def Materials.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["materials"]

#leanify_article Materials "article.tex" "fnv1a64:8f8dc472b43b7fc6" with Materials.vocabulary
