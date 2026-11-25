import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `populationdynamics`: exponential and logistic growth, doubling times, sustainable yields, harvesting, the Ricker and Beverton-Holt maps and Lotka-Volterra equilibria. After editing the article, run

    lake exe leanify prepare tests/PopulationDynamics/article.tex --lean tests/PopulationDynamics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `populationdynamics`. -/
def PopulationDynamics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["populationdynamics"]

#leanify_article PopulationDynamics "article.tex" "fnv1a64:d0119572a4fe195b" with PopulationDynamics.vocabulary
