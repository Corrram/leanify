import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `polynomials` of the vocabulary: polynomials as real functions, modifiers with an argument (`a polynomial $p$ of degree $n$`), the symbol `\deg` with its domain, and products of functions value by value. After editing the article, run

    lake exe leanify prepare tests/Polynomials/article.tex --lean tests/Polynomials/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `polynomials`. -/
def Polynomials.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["polynomials"]

#leanify_article Polynomials "article.tex" "fnv1a64:e1d7895f14633e68" with Polynomials.vocabulary
