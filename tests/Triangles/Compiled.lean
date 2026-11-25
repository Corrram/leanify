import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `triangles`: semiperimeter, Heron's area, angles, in- and circumradius, altitudes, medians and bisectors of a triangle by its sides, and regular polygons. After editing the article, run

    lake exe leanify prepare tests/Triangles/article.tex --lean tests/Triangles/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `triangles`. -/
def Triangles.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["triangles"]

#leanify_article Triangles "article.tex" "fnv1a64:08feb1de63353c58" with Triangles.vocabulary
