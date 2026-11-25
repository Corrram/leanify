import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `mechanics`: projectiles, pendulums, oscillators and damping ratios, kinetic energy, orbital speeds, escape velocities and Kepler's third law. After editing the article, run

    lake exe leanify prepare tests/Mechanics/article.tex --lean tests/Mechanics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `mechanics`. -/
def Mechanics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["mechanics"]

#leanify_article Mechanics "article.tex" "fnv1a64:24032b4ff08585bd" with Mechanics.vocabulary
