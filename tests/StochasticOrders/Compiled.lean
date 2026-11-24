import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `stochasticorders`: the usual, hazard rate, likelihood ratio, convex and increasing convex orders of densities (`$f$ is smaller than $g$ in the hazard rate order`, not a comparison of numbers). After editing the article, run

    lake exe leanify prepare tests/StochasticOrders/article.tex --lean tests/StochasticOrders/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `densities`, `risk` and `stochasticorders`. -/
def StochasticOrders.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["densities", "risk", "stochasticorders"]

#leanify_article StochasticOrders "article.tex" "fnv1a64:3352ba090a4e6d85" with StochasticOrders.vocabulary
