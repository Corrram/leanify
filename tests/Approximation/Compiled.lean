import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `approximation`: errors, the condition number, rounding, difference quotients, quadrature rules and interpolation. After editing the article, run

    lake exe leanify prepare tests/Approximation/article.tex --lean tests/Approximation/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `approximation`. -/
def Approximation.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "approximation"]

#leanify_article Approximation "article.tex" "fnv1a64:d08f9de15a17d9b8" with Approximation.vocabulary
