import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `functionalequations`: additive, subadditive, midpoint convex, Jensen-affine, involutive, idempotent and homogeneous functions, and d'Alembert's equation. After editing the article, run

    lake exe leanify prepare tests/FunctionalEquations/article.tex --lean tests/FunctionalEquations/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `functionalequations`. -/
def FunctionalEquations.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["functionalequations"]

#leanify_article FunctionalEquations "article.tex" "fnv1a64:d11b56b89b35fb23" with FunctionalEquations.vocabulary
