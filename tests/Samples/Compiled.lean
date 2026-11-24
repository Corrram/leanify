import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `samples`: the sample mean and variance, order statistics and the median, the sample correlation and the least-squares slope of the first `n` terms of a sequence. After editing the article, run

    lake exe leanify prepare tests/Samples/article.tex --lean tests/Samples/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `samples`. -/
def Samples.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["samples"]

#leanify_article Samples "article.tex" "fnv1a64:f77e9f80f270892c" with Samples.vocabulary
