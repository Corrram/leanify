import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `testing`: z- and t-statistics, one- and two-sided p-values, normal quantiles, margins of error and the chi-squared statistic. After editing the article, run

    lake exe leanify prepare tests/Testing/article.tex --lean tests/Testing/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `testing`. -/
def Testing.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["testing"]

#leanify_article Testing "article.tex" "fnv1a64:343ab3a995ed1cd2" with Testing.vocabulary
