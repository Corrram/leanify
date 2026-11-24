import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `risk`: the survival function, hazard rate and quantile function of a density, the value at risk and the expected shortfall at a level, and monotone failure rates. After editing the article, run

    lake exe leanify prepare tests/Risk/article.tex --lean tests/Risk/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `densities` and `risk`. -/
def Risk.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["densities", "risk"]

#leanify_article Risk "article.tex" "fnv1a64:a1bd0bd9d6f16669" with Risk.vocabulary
