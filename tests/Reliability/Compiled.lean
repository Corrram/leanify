import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `reliability`: series, parallel, k-out-of-n and bridge systems, exponential lifetimes, mean times to failure and availability. After editing the article, run

    lake exe leanify prepare tests/Reliability/article.tex --lean tests/Reliability/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `reliability`. -/
def Reliability.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["reliability"]

#leanify_article Reliability "article.tex" "fnv1a64:d7a2051eb77ab21d" with Reliability.vocabulary
