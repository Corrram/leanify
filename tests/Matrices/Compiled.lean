import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `matrices` of the vocabulary: a type of its own whose notation is defined for matrices of matching sizes (`A+B`, `AB`, `A^{-1}`), the transpose `A^\top`, `\det`, `\operatorname{tr}`, `\operatorname{rank}`, and modifiers with arguments (`an $n\times n$ matrix`). After editing the article, run

    lake exe leanify prepare tests/Matrices/article.tex --lean tests/Matrices/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `matrices`. -/
def Matrices.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["matrices"]

#leanify_article Matrices "article.tex" "fnv1a64:decfbd0e0670b287" with Matrices.vocabulary
