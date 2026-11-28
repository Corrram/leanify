import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `vectors` of the vocabulary: a type of its own with `\lVert x\rVert` and `\langle x,y\rangle` as its methods, sums of vectors of the same dimension, multiples, and a modifier whose argument is a vector (`orthogonal to $y$`). After editing the article, run

    lake exe leanify prepare tests/Vectors/article.tex --lean tests/Vectors/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `vectors`. -/
def Vectors.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["vectors"]

#leanify_article Vectors "article.tex" "fnv1a64:be3a9ee73ec60b95" with Vectors.vocabulary
