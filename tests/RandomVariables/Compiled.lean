import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `randomvariables`: expectations, variances, covariances and probabilities of real random variables, independence and identical distribution, the standard distributions by their distribution functions, events and conditional probabilities. After editing the article, run

    lake exe leanify prepare tests/RandomVariables/article.tex --lean tests/RandomVariables/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `randomvariables`. -/
def RandomVariables.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["randomvariables"]

#leanify_article RandomVariables "article.tex" "fnv1a64:125ab8473e19d9f0" with RandomVariables.vocabulary
