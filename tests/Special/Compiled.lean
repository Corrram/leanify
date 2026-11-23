import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `special` of the vocabulary: the symbols `\Gamma` and `\zeta` with their domains, the beta function, the Bernoulli numbers and two constants. After editing the article, run

    lake exe leanify prepare tests/Special/article.tex --lean tests/Special/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `special`. -/
def Special.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["special"]

#leanify_article Special "article.tex" "fnv1a64:3b3fa6e90b22f940" with Special.vocabulary
