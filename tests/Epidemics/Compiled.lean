import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `epidemics`: basic reproduction numbers, herd immunity thresholds, final sizes, doubling times, vaccination coverage and the SIS model. After editing the article, run

    lake exe leanify prepare tests/Epidemics/article.tex --lean tests/Epidemics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `epidemics`. -/
def Epidemics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["epidemics"]

#leanify_article Epidemics "article.tex" "fnv1a64:c77ac689cd78a105" with Epidemics.vocabulary
