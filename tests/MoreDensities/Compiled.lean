import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the further densities of the field `densities`: lognormal, Student t, Rayleigh, Gumbel, generalized Pareto and triangular, and the skewness. After editing the article, run

    lake exe leanify prepare tests/MoreDensities/article.tex --lean tests/MoreDensities/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `densities`. -/
def MoreDensities.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["densities"]

#leanify_article MoreDensities "article.tex" "fnv1a64:29c5df0f0280c74e" with MoreDensities.vocabulary
