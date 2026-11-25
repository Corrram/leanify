import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `electromagnetism`: Coulomb forces, fields and potentials of point charges, capacitors, magnetic fields of wires and solenoids, magnetic forces, cyclotron frequencies and Larmor radii. After editing the article, run

    lake exe leanify prepare tests/Electromagnetism/article.tex --lean tests/Electromagnetism/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `electromagnetism`. -/
def Electromagnetism.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["electromagnetism"]

#leanify_article Electromagnetism "article.tex" "fnv1a64:f348db1413b5a4e6" with Electromagnetism.vocabulary
