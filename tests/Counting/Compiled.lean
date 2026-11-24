import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `counting`: subsets, permutations, multisets, maps, surjections, compositions and lattice paths. After editing the article, run

    lake exe leanify prepare tests/Counting/article.tex --lean tests/Counting/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `counting`. -/
def Counting.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["counting"]

#leanify_article Counting "article.tex" "fnv1a64:a1a63e932a440190" with Counting.vocabulary
