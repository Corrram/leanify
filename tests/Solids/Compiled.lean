import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `solids`: volumes of balls and areas of spheres in n dimensions, cylinders, cones, ellipsoids, tori, regular polyhedra and the standard simplex. After editing the article, run

    lake exe leanify prepare tests/Solids/article.tex --lean tests/Solids/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `solids`. -/
def Solids.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["solids"]

#leanify_article Solids "article.tex" "fnv1a64:7121d9802d98b31c" with Solids.vocabulary
