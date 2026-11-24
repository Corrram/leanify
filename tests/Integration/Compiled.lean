import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `integration`: `$p$-integrable` functions and `L^p` norms, the essential supremum, improper integrals as limits, the integral on a set. After editing the article, run

    lake exe leanify prepare tests/Integration/article.tex --lean tests/Integration/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions`, `realsets` and `integration`. -/
def Integration.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "realsets", "integration"]

#leanify_article Integration "article.tex" "fnv1a64:711fb0bc03ad2f20" with Integration.vocabulary
