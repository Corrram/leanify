import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `odes`: solutions of first-order linear, separable, Bernoulli and Riccati equations, of second-order linear, Euler-Cauchy and oscillator equations, and the Wronskian. After editing the article, run

    lake exe leanify prepare tests/Odes/article.tex --lean tests/Odes/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `odes`. -/
def Odes.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["odes"]

#leanify_article Odes "article.tex" "fnv1a64:6d994af46d8ad4e4" with Odes.vocabulary
