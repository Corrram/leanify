import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `latticepoints`: lattice points in disks and balls, on segments and visible from the origin, and Pick's theorem. After editing the article, run

    lake exe leanify prepare tests/LatticePoints/article.tex --lean tests/LatticePoints/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `latticepoints`. -/
def LatticePoints.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["latticepoints"]

#leanify_article LatticePoints "article.tex" "fnv1a64:756e3a77a435cfbc" with LatticePoints.vocabulary
