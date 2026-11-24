import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `optimization`: minimizers of a function as modifiers of points (`$x$ is a local minimizer of $f$`), extreme values as descriptions, the convex conjugate and the Moreau envelope. After editing the article, run

    lake exe leanify prepare tests/Optimization/article.tex --lean tests/Optimization/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `optimization`. -/
def Optimization.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "optimization"]

#leanify_article Optimization "article.tex" "fnv1a64:8650393772a3b02e" with Optimization.vocabulary
