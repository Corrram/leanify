import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `concentration`: Markov, Chebyshev, Cantelli, Hoeffding, Bernstein, Chernoff and McDiarmid bounds, Hoeffding sample sizes and the sample complexity of finite hypothesis classes. After editing the article, run

    lake exe leanify prepare tests/Concentration/article.tex --lean tests/Concentration/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `concentration`. -/
def Concentration.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["concentration"]

#leanify_article Concentration "article.tex" "fnv1a64:129cb5cc9a15a8e6" with Concentration.vocabulary
