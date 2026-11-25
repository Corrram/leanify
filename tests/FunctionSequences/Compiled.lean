import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `functionsequences`: pointwise and uniform convergence, uniform Cauchy, boundedness and equicontinuity of sequences of functions, supremum distances and partial sums. After editing the article, run

    lake exe leanify prepare tests/FunctionSequences/article.tex --lean tests/FunctionSequences/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `functionsequences`. -/
def FunctionSequences.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["functionsequences"]

#leanify_article FunctionSequences "article.tex" "fnv1a64:65705f0128dce044" with FunctionSequences.vocabulary
