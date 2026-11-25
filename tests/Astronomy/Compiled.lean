import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `astronomy`: parallax distances, distance moduli, magnitudes, redshifts, Hubble's law, Schwarzschild radii, luminosities and Wien's law. After editing the article, run

    lake exe leanify prepare tests/Astronomy/article.tex --lean tests/Astronomy/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `astronomy`. -/
def Astronomy.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["astronomy"]

#leanify_article Astronomy "article.tex" "fnv1a64:9d12d5e0d640f952" with Astronomy.vocabulary
