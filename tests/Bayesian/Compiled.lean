import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `bayesian`: posteriors of the beta-binomial, gamma-Poisson and normal-normal families, Bayes' formula and the Bayes factor. After editing the article, run

    lake exe leanify prepare tests/Bayesian/article.tex --lean tests/Bayesian/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `bayesian`. -/
def Bayesian.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["bayesian"]

#leanify_article Bayesian "article.tex" "fnv1a64:ea3843a00b74ef30" with Bayesian.vocabulary
