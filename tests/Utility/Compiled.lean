import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `utility`: risk averse utility functions, Arrow-Pratt coefficients, CARA and CRRA utilities, expected utility, certainty equivalents and risk premia. After editing the article, run

    lake exe leanify prepare tests/Utility/article.tex --lean tests/Utility/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `utility`. -/
def Utility.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["utility"]

#leanify_article Utility "article.tex" "fnv1a64:239149db2c73e113" with Utility.vocabulary
