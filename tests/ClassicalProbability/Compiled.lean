import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `classicalprobability`: the birthday, coupon collector, ballot, derangement, Buffon's needle and secretary problems. After editing the article, run

    lake exe leanify prepare tests/ClassicalProbability/article.tex --lean tests/ClassicalProbability/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `classicalprobability`. -/
def ClassicalProbability.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["classicalprobability"]

#leanify_article ClassicalProbability "article.tex" "fnv1a64:07c22aa04d66d995" with ClassicalProbability.vocabulary
