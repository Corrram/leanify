import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `majorization`: majorized, weakly sub- and supermajorized and decreasingly ordered vectors, the k-th largest coordinate and the sums of the largest coordinates. After editing the article, run

    lake exe leanify prepare tests/Majorization/article.tex --lean tests/Majorization/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `majorization`. -/
def Majorization.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["majorization"]

#leanify_article Majorization "article.tex" "fnv1a64:04b68876cb9c9cc5" with Majorization.vocabulary
