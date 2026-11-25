import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `convergence`: bisection and contraction step counts, Richardson and Aitken extrapolation, estimated orders and correct digits. After editing the article, run

    lake exe leanify prepare tests/Convergence/article.tex --lean tests/Convergence/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `convergence`. -/
def Convergence.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["convergence"]

#leanify_article Convergence "article.tex" "fnv1a64:bf52cc9c84891877" with Convergence.vocabulary
