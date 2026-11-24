import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `odesolvers`: solutions of an initial value problem, Lipschitz right-hand sides, and the Euler, Heun and Runge–Kutta steps. After editing the article, run

    lake exe leanify prepare tests/OdeSolvers/article.tex --lean tests/OdeSolvers/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `odesolvers`. -/
def OdeSolvers.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "odesolvers"]

#leanify_article OdeSolvers "article.tex" "fnv1a64:e15b602e8b0e02bb" with OdeSolvers.vocabulary
