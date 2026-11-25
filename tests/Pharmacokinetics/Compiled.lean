import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `pharmacokinetics`: the one-compartment model: concentrations, clearance, half-lives, areas under the curve, steady states, accumulation and loading doses. After editing the article, run

    lake exe leanify prepare tests/Pharmacokinetics/article.tex --lean tests/Pharmacokinetics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `pharmacokinetics`. -/
def Pharmacokinetics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["pharmacokinetics"]

#leanify_article Pharmacokinetics "article.tex" "fnv1a64:5f64eb6e9ec3e102" with Pharmacokinetics.vocabulary
