import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `populationgenetics`: Hardy-Weinberg frequencies, selection, Moran and Kimura fixation probabilities, drift, effective sizes and mutation equilibria. After editing the article, run

    lake exe leanify prepare tests/PopulationGenetics/article.tex --lean tests/PopulationGenetics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `populationgenetics`. -/
def PopulationGenetics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["populationgenetics"]

#leanify_article PopulationGenetics "article.tex" "fnv1a64:d545f7418f3a94e4" with PopulationGenetics.vocabulary
