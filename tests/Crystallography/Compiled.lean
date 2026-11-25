import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `crystallography`: interplanar spacings, packing fractions, coordination numbers and nearest-neighbour distances of cubic lattices. After editing the article, run

    lake exe leanify prepare tests/Crystallography/article.tex --lean tests/Crystallography/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `crystallography`. -/
def Crystallography.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["crystallography"]

#leanify_article Crystallography "article.tex" "fnv1a64:ed7f47524ce40347" with Crystallography.vocabulary
