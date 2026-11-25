import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `relativity`: Lorentz factors, rapidities, relativistic velocity addition, time dilation, length contraction, energy, momentum and redshift. After editing the article, run

    lake exe leanify prepare tests/Relativity/article.tex --lean tests/Relativity/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `relativity`. -/
def Relativity.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["relativity"]

#leanify_article Relativity "article.tex" "fnv1a64:8cdff125dea47e10" with Relativity.vocabulary
