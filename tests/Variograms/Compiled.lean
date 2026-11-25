import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `variograms`: spherical, exponential, Gaussian and power variograms, nuggets, covariances and practical ranges. After editing the article, run

    lake exe leanify prepare tests/Variograms/article.tex --lean tests/Variograms/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `variograms`. -/
def Variograms.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["variograms"]

#leanify_article Variograms "article.tex" "fnv1a64:bd45106b593d36c4" with Variograms.vocabulary
