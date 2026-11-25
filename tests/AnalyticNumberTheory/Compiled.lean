import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `analyticnumbertheory`: the von Mangoldt function, Chebyshev's functions, the logarithmic integral, primes in residue classes, twin primes and prime gaps. After editing the article, run

    lake exe leanify prepare tests/AnalyticNumberTheory/article.tex --lean tests/AnalyticNumberTheory/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `analyticnumbertheory`. -/
def AnalyticNumberTheory.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["analyticnumbertheory"]

#leanify_article AnalyticNumberTheory "article.tex" "fnv1a64:b29c371c1fc8b7a7" with AnalyticNumberTheory.vocabulary
