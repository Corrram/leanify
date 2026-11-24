import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `iteration`: the Newton map, Newton and fixed-point sequences, and orders of convergence. After editing the article, run

    lake exe leanify prepare tests/Iteration/article.tex --lean tests/Iteration/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `iteration`. -/
def Iteration.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "iteration"]

#leanify_article Iteration "article.tex" "fnv1a64:8d719fa30530010e" with Iteration.vocabulary
