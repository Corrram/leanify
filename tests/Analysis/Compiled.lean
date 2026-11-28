import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `realfunctions` of the vocabulary: real functions bound by a noun with their properties (`a continuous periodic function`, `a $1$-Lipschitz function`), `Every NP $x$ is ADJ`, and notions with domains (the Lipschitz constant, the total variation). After editing the article, run

    lake exe leanify prepare tests/Analysis/article.tex --lean tests/Analysis/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `realfunctions`. -/
def Analysis.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions"]

#leanify_article Analysis "article.tex" "fnv1a64:adfde78858f976fa" with Analysis.vocabulary
