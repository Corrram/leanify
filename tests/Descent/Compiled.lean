import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `descent`: Armijo and Wolfe steps, descent directions, and gradient descent, heavy-ball and proximal point sequences. After editing the article, run

    lake exe leanify prepare tests/Descent/article.tex --lean tests/Descent/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `descent`. -/
def Descent.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["descent"]

#leanify_article Descent "article.tex" "fnv1a64:361a097ee4f94404" with Descent.vocabulary
