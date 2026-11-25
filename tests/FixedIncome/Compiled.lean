import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `fixedincome`: bond prices, durations, current yields, perpetuities, effective rates and loans. After editing the article, run

    lake exe leanify prepare tests/FixedIncome/article.tex --lean tests/FixedIncome/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `fixedincome`. -/
def FixedIncome.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["fixedincome"]

#leanify_article FixedIncome "article.tex" "fnv1a64:85fab53206b1bffa" with FixedIncome.vocabulary
