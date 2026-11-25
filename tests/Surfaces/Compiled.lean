import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `surfaces`: Euler characteristics and genera of closed surfaces, Gauss-Bonnet, curvatures of spheres and cylinders, and the torus. After editing the article, run

    lake exe leanify prepare tests/Surfaces/article.tex --lean tests/Surfaces/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `surfaces`. -/
def Surfaces.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["surfaces"]

#leanify_article Surfaces "article.tex" "fnv1a64:eae135ee4455ff09" with Surfaces.vocabulary
