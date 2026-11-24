import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `matrixnorms`, which includes `matrices`: Frobenius and maximum norms, condition numbers, diagonal dominance and band structure. After editing the article, run

    lake exe leanify prepare tests/MatrixNorms/article.tex --lean tests/MatrixNorms/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `matrixnorms`. -/
def MatrixNorms.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["matrixnorms"]

#leanify_article MatrixNorms "article.tex" "fnv1a64:ff14bbc5eeb0d0f1" with MatrixNorms.vocabulary
