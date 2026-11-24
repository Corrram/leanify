import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `densities`: probability densities by a noun, the standard densities with their parameters, and notions of a density (its mean, variance, moment generating function `M_f` at `t`, with the domain of `t`). After editing the article, run

    lake exe leanify prepare tests/Densities/article.tex --lean tests/Densities/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `densities`. -/
def Densities.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["densities"]

#leanify_article Densities "article.tex" "fnv1a64:70f298cb43c3b31a" with Densities.vocabulary
