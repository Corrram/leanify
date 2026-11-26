import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `arithmetic` of the vocabulary: arithmetic functions as notions (`Euler's totient function`, `the $p$-adic valuation of $n$`), perfect numbers, Mersenne primes and multiplicative functions. After editing the article, run

    lake exe leanify prepare tests/Arithmetic/article.tex --lean tests/Arithmetic/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `numbers` and `arithmetic`. -/
def Arithmetic.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["numbers", "arithmetic"]

#leanify_article Arithmetic "article.tex" "fnv1a64:688a164184aa4d61" with Arithmetic.vocabulary
