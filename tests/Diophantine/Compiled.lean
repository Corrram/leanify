import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `diophantine`: Frobenius numbers, numerical semigroups, representations by linear forms and as sums of two squares, Euclid's formula and congruent numbers. After editing the article, run

    lake exe leanify prepare tests/Diophantine/article.tex --lean tests/Diophantine/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `diophantine`. -/
def Diophantine.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["diophantine"]

#leanify_article Diophantine "article.tex" "fnv1a64:19c7c6a471e4b1ed" with Diophantine.vocabulary
