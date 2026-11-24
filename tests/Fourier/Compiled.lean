import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `fourier`: Fourier coefficients and partial sums of a function, the Dirichlet and Fejér kernels, the cosine transform, trigonometric polynomials. After editing the article, run

    lake exe leanify prepare tests/Fourier/article.tex --lean tests/Fourier/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `fourier`. -/
def Fourier.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "fourier"]

#leanify_article Fourier "article.tex" "fnv1a64:b5d659a1c6dcb6e5" with Fourier.vocabulary
