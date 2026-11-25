import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `summability`: Cesàro and Abel summability, convergent, null, Cauchy, eventually nondecreasing and bounded-variation sequences, subadditive and log-concave sequences, Cesàro means and forward differences. After editing the article, run

    lake exe leanify prepare tests/Summability/article.tex --lean tests/Summability/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `summability`. -/
def Summability.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["summability"]

#leanify_article Summability "article.tex" "fnv1a64:ed3e77a3f0f17b27" with Summability.vocabulary
