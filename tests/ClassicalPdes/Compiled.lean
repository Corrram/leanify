import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `classicalpdes`: solutions of the heat, wave, transport, Laplace and Burgers equations, partial derivatives, the heat kernel and d'Alembert's formula. After editing the article, run

    lake exe leanify prepare tests/ClassicalPdes/article.tex --lean tests/ClassicalPdes/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `classicalpdes`. -/
def ClassicalPdes.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["classicalpdes"]

#leanify_article ClassicalPdes "article.tex" "fnv1a64:b9fd998c0dc524e2" with ClassicalPdes.vocabulary
