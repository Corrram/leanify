import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the further distributions of the field `distributions`: geometric, Bernoulli and discrete uniform, the variance and the probability generating function. After editing the article, run

    lake exe leanify prepare tests/MoreDistributions/article.tex --lean tests/MoreDistributions/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `distributions`. -/
def MoreDistributions.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["distributions"]

#leanify_article MoreDistributions "article.tex" "fnv1a64:3603024dd28747e9" with MoreDistributions.vocabulary
