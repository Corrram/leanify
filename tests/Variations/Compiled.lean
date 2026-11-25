import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `variations`: actions of Lagrangians, the Euler-Lagrange equation, minimizers with fixed endpoint values, arc length, Dirichlet energy and the Hamiltonian. After editing the article, run

    lake exe leanify prepare tests/Variations/article.tex --lean tests/Variations/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `variations`. -/
def Variations.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["variations"]

#leanify_article Variations "article.tex" "fnv1a64:92c8787a789727ca" with Variations.vocabulary
