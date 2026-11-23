import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `geometry` of the vocabulary: points of the plane, a variable that is the value of a notion (`let $M$ be the midpoint of $A$ and $B$`), phrases with commas (`the triangle with vertices $A$, $B$ and $C$`), and figures as sets of points (`a point $P$ lying on $\Gamma(A,2)$`). After editing the article, run

    lake exe leanify prepare tests/Geometry/article.tex --lean tests/Geometry/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `geometry`. -/
def Geometry.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["geometry"]

#leanify_article Geometry "article.tex" "fnv1a64:9f46492c2e7110f7" with Geometry.vocabulary
