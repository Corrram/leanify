import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `digits`: digits in base b, the number of digits, reversals, palindromes, digital roots, repunits, Harshad and narcissistic numbers. After editing the article, run

    lake exe leanify prepare tests/Digits/article.tex --lean tests/Digits/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `digits`. -/
def Digits.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["digits"]

#leanify_article Digits "article.tex" "fnv1a64:89440aaeea14e8f3" with Digits.vocabulary
