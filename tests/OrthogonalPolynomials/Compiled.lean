import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `orthogonalpolynomials`: Legendre, Hermite, Laguerre and Chebyshev polynomials of degree `n` by their explicit sums. After editing the article, run

    lake exe leanify prepare tests/OrthogonalPolynomials/article.tex --lean tests/OrthogonalPolynomials/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `orthogonalpolynomials`. -/
def OrthogonalPolynomials.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["orthogonalpolynomials"]

#leanify_article OrthogonalPolynomials "article.tex" "fnv1a64:94cf64674d956250" with OrthogonalPolynomials.vocabulary
