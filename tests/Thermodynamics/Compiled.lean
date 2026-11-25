import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `thermodynamics`: Carnot efficiencies, ideal gases, Newton's law of cooling, entropy changes, black-body radiation and Boltzmann factors. After editing the article, run

    lake exe leanify prepare tests/Thermodynamics/article.tex --lean tests/Thermodynamics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `thermodynamics`. -/
def Thermodynamics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["thermodynamics"]

#leanify_article Thermodynamics "article.tex" "fnv1a64:4b1d3102eaafd6e9" with Thermodynamics.vocabulary
