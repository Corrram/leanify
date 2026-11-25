import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `geometricprobability`: expected distances between random points, the expected area of a random triangle and the probability of an acute triangle, as integrals. After editing the article, run

    lake exe leanify prepare tests/GeometricProbability/article.tex --lean tests/GeometricProbability/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `geometricprobability`. -/
def GeometricProbability.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["geometricprobability"]

#leanify_article GeometricProbability "article.tex" "fnv1a64:9cfa37fa2f230eec" with GeometricProbability.vocabulary
