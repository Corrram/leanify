import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `curves`: speed, curvature, length and signed area of parametrized plane curves, curvature of graphs, polar area and length, regular and singular points. After editing the article, run

    lake exe leanify prepare tests/Curves/article.tex --lean tests/Curves/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `curves`. -/
def Curves.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["curves"]

#leanify_article Curves "article.tex" "fnv1a64:5b26f6630e50804b" with Curves.vocabulary
