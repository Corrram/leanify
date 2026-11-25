import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of conditions in binders: a condition on some of the variables, and lists of conditions that restate variables bound before (`with $a\ge0$, $b\ge0$ and $a<1$`). After editing the article, run

    lake exe leanify prepare tests/Conditions/article.tex --lean tests/Conditions/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core. -/
def Conditions.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select []

#leanify_article Conditions "article.tex" "fnv1a64:0d26fffd588b13de" with Conditions.vocabulary
