import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `information`: entropy and divergences of probability distributions on `ℕ₀`. After editing the article, run

    lake exe leanify prepare tests/Information/article.tex --lean tests/Information/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `distributions` and `information`. -/
def Information.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["distributions", "information"]

#leanify_article Information "article.tex" "fnv1a64:e43c7696e674c7f7" with Information.vocabulary
