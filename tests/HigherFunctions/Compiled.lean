import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `higherfunctions`: error functions, Bessel functions, the incomplete gamma, Lambert W, dilogarithm, sine and Fresnel integrals and Dawson's function. After editing the article, run

    lake exe leanify prepare tests/HigherFunctions/article.tex --lean tests/HigherFunctions/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `higherfunctions`. -/
def HigherFunctions.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["higherfunctions"]

#leanify_article HigherFunctions "article.tex" "fnv1a64:f86bf6c02b560611" with HigherFunctions.vocabulary
