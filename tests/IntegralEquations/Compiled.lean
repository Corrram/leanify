import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `integralequations`: solutions of Volterra, Fredholm and Abel integral equations, symmetric and Volterra kernels, iterated kernels and the integral operator. After editing the article, run

    lake exe leanify prepare tests/IntegralEquations/article.tex --lean tests/IntegralEquations/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `integralequations`. -/
def IntegralEquations.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["integralequations"]

#leanify_article IntegralEquations "article.tex" "fnv1a64:d9f7d25d51a3f957" with IntegralEquations.vocabulary
