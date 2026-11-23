import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `permutations` of the vocabulary: a type of its own with an application to numbers (`\sigma(i)`), a composition defined for permutations of the same degree, powers, and the sign. After editing the article, run

    lake exe leanify prepare tests/Permutations/article.tex --lean tests/Permutations/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `permutations`. -/
def Permutations.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["permutations"]

#leanify_article Permutations "article.tex" "fnv1a64:eac94f375a968827" with Permutations.vocabulary
