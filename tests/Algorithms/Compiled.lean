import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `algorithms`: comparisons of binary search, insertion sort, merge sort and quicksort, the sorting lower bound, the Tower of Hanoi, the master theorem exponent and binary trees. After editing the article, run

    lake exe leanify prepare tests/Algorithms/article.tex --lean tests/Algorithms/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `algorithms`. -/
def Algorithms.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["algorithms"]

#leanify_article Algorithms "article.tex" "fnv1a64:428c95cfb7d83a71" with Algorithms.vocabulary
