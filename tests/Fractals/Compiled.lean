import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `fractals`: similarity dimensions (Moran's equation), the Cantor set, the Koch curve and snowflake, the Sierpinski triangle and the Menger sponge. After editing the article, run

    lake exe leanify prepare tests/Fractals/article.tex --lean tests/Fractals/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `fractals`. -/
def Fractals.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["fractals"]

#leanify_article Fractals "article.tex" "fnv1a64:4701df576048be18" with Fractals.vocabulary
