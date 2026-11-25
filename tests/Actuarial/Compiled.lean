import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `actuarial`: Gompertz and Gompertz-Makeham survival, life expectancies, net single premiums, annuities and pure endowments. After editing the article, run

    lake exe leanify prepare tests/Actuarial/article.tex --lean tests/Actuarial/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `actuarial`. -/
def Actuarial.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["actuarial"]

#leanify_article Actuarial "article.tex" "fnv1a64:c93eebcaf170aad1" with Actuarial.vocabulary
