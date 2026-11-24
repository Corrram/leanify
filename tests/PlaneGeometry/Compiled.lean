import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `planegeometry`, which includes `geometry`: distances to lines, triangle centres described by their property, conics by their foci, a modifier with two arguments after `and` (`collinear with $B$ and $C$`). After editing the article, run

    lake exe leanify prepare tests/PlaneGeometry/article.tex --lean tests/PlaneGeometry/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `planegeometry`. -/
def PlaneGeometry.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["planegeometry"]

#leanify_article PlaneGeometry "article.tex" "fnv1a64:eeeaced6aed58226" with PlaneGeometry.vocabulary
