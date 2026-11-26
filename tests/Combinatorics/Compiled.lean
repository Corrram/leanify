import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `combinatorics` of the vocabulary: counting numbers as notions with arguments (`the $n$th Catalan number`, `the number of partitions of a set of $n$ elements into $k$ blocks`), with the notation the article gives them. After editing the article, run

    lake exe leanify prepare tests/Combinatorics/article.tex --lean tests/Combinatorics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `combinatorics`. -/
def Combinatorics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["combinatorics"]

#leanify_article Combinatorics "article.tex" "fnv1a64:086997ddb33c6a5d" with Combinatorics.vocabulary
