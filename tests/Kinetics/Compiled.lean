import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `kinetics`: concentrations in reactions of order zero, one and two, half-lives, decay constants, Arrhenius and Michaelis-Menten rates and the pH. After editing the article, run

    lake exe leanify prepare tests/Kinetics/article.tex --lean tests/Kinetics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `kinetics`. -/
def Kinetics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["kinetics"]

#leanify_article Kinetics "article.tex" "fnv1a64:45fbbea0c8043fd6" with Kinetics.vocabulary
