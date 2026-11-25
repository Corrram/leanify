import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `options`: payoffs, forward prices, put-call parity and the binomial model. After editing the article, run

    lake exe leanify prepare tests/Options/article.tex --lean tests/Options/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `options`. -/
def Options.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["options"]

#leanify_article Options "article.tex" "fnv1a64:95e23e4c75dc7408" with Options.vocabulary
