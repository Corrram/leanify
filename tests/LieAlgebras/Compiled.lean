import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `liealgebras`: dimensions, positive roots and Coxeter numbers of the classical simple Lie algebras. After editing the article, run

    lake exe leanify prepare tests/LieAlgebras/article.tex --lean tests/LieAlgebras/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `liealgebras`. -/
def LieAlgebras.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["liealgebras"]

#leanify_article LieAlgebras "article.tex" "fnv1a64:f9e61c4d2392d676" with LieAlgebras.vocabulary
