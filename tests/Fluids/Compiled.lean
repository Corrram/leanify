import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `fluids`: Reynolds and Froude numbers, hydrostatic and dynamic pressure, Torricelli's law, Poiseuille flow, drag and Stokes terminal velocity. After editing the article, run

    lake exe leanify prepare tests/Fluids/article.tex --lean tests/Fluids/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `fluids`. -/
def Fluids.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["fluids"]

#leanify_article Fluids "article.tex" "fnv1a64:726474c7eda47303" with Fluids.vocabulary
