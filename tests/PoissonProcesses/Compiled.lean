import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `poissonprocesses`: arrival probabilities, waiting times, thinning and compound Poisson sums. After editing the article, run

    lake exe leanify prepare tests/PoissonProcesses/article.tex --lean tests/PoissonProcesses/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `poissonprocesses`. -/
def PoissonProcesses.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["poissonprocesses"]

#leanify_article PoissonProcesses "article.tex" "fnv1a64:bce71f432c320cff" with PoissonProcesses.vocabulary
