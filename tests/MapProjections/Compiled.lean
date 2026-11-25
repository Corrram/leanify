import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `mapprojections`: Mercator, Lambert equal-area, sinusoidal and stereographic projections. After editing the article, run

    lake exe leanify prepare tests/MapProjections/article.tex --lean tests/MapProjections/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `mapprojections`. -/
def MapProjections.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["mapprojections"]

#leanify_article MapProjections "article.tex" "fnv1a64:3d12ef9c6e7a3d80" with MapProjections.vocabulary
