import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `calculus`: higher derivatives as constants (`a $3$ times differentiable function`), the Taylor polynomial, inflection points, and integrals on `[a,b]` whose domains speak of three arguments before. After editing the article, run

    lake exe leanify prepare tests/CalculusField/article.tex --lean tests/CalculusField/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions`, `optimization` and `calculus`. -/
def CalculusField.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "optimization", "calculus"]

#leanify_article CalculusField "article.tex" "fnv1a64:e53ec5ad94a4c2ae" with CalculusField.vocabulary
