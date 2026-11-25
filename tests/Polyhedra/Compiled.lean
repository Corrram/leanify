import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `polyhedra`: Euler characteristics, the vertices, edges, faces and dihedral angles of the Platonic solids, and angle defects. After editing the article, run

    lake exe leanify prepare tests/Polyhedra/article.tex --lean tests/Polyhedra/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `polyhedra`. -/
def Polyhedra.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["polyhedra"]

#leanify_article Polyhedra "article.tex" "fnv1a64:d0f5df1f7cd1de4c" with Polyhedra.vocabulary
