import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `sphericalgeometry`: central angles by latitude and longitude, chords, spherical excess and Girard's theorem, spherical caps and solid angles. After editing the article, run

    lake exe leanify prepare tests/SphericalGeometry/article.tex --lean tests/SphericalGeometry/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `sphericalgeometry`. -/
def SphericalGeometry.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["sphericalgeometry"]

#leanify_article SphericalGeometry "article.tex" "fnv1a64:39c0f5563ffcfa5e" with SphericalGeometry.vocabulary
