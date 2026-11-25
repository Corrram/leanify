import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `extremes`: GEV, Gumbel, Fréchet and Weibull distribution functions, return levels, generalized Pareto distributions and maximum domains of attraction. After editing the article, run

    lake exe leanify prepare tests/Extremes/article.tex --lean tests/Extremes/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `extremes`. -/
def Extremes.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["extremes"]

#leanify_article Extremes "article.tex" "fnv1a64:cb4ac918f0439d18" with Extremes.vocabulary
