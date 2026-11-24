import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `finance`: interest, annuities and the Black–Scholes formulas, notions with five arguments in one phrase. After editing the article, run

    lake exe leanify prepare tests/Finance/article.tex --lean tests/Finance/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `finance`. -/
def Finance.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["finance"]

#leanify_article Finance "article.tex" "fnv1a64:f5f76032d268dd17" with Finance.vocabulary
