import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `economics`: elasticities, marginal and average values, Cobb-Douglas and CES functions, returns to scale, Lorenz curves, the Gini coefficient and consumer surplus. After editing the article, run

    lake exe leanify prepare tests/Economics/article.tex --lean tests/Economics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `economics`. -/
def Economics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["economics"]

#leanify_article Economics "article.tex" "fnv1a64:08b0f7b9da96f6c9" with Economics.vocabulary
