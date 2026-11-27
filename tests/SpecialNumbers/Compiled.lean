import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `specialnumbers`: twin, Sophie Germain, safe and Fermat primes, perfect powers, sums of two squares, Fermat and Mersenne numbers, figurate numbers. After editing the article, run

    lake exe leanify prepare tests/SpecialNumbers/article.tex --lean tests/SpecialNumbers/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `numbers` and `specialnumbers`. -/
def SpecialNumbers.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["numbers", "specialnumbers"]

#leanify_article SpecialNumbers "article.tex" "fnv1a64:4ba7d6be6f4edf4d" with SpecialNumbers.vocabulary
