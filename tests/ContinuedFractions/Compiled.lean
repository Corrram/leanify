import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `continuedfractions`: complete and partial quotients and convergents of an irrational number, finite continued fractions, badly approximable numbers, Liouville numbers, quadratic irrationals and best approximations. After editing the article, run

    lake exe leanify prepare tests/ContinuedFractions/article.tex --lean tests/ContinuedFractions/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `continuedfractions`. -/
def ContinuedFractions.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["continuedfractions"]

#leanify_article ContinuedFractions "article.tex" "fnv1a64:8e1f2f52416609ad" with ContinuedFractions.vocabulary
