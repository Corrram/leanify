import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `copulas`, which includes `markov`: the Fréchet–Hoeffding bounds and the named copula families, Spearman's rho, Kendall's tau, Blomqvist's beta and Chatterjee's xi, tail dependence, quadrant dependence and max-stability. After editing the article, run

    lake exe leanify prepare tests/Copulas/article.tex --lean tests/Copulas/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `copulas`. -/
def Copulas.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["copulas"]

#leanify_article Copulas "article.tex" "fnv1a64:2083caf50122cf8c" with Copulas.vocabulary
