import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `regression`: fitted values, residuals, sums of squares, the coefficient of determination and standard errors of the least-squares line. After editing the article, run

    lake exe leanify prepare tests/Regression/article.tex --lean tests/Regression/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `regression`. -/
def Regression.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["regression"]

#leanify_article Regression "article.tex" "fnv1a64:dd7d64716e58dee3" with Regression.vocabulary
