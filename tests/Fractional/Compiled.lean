import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `fractional`: Riemann-Liouville, Hadamard and Caputo fractional integrals and derivatives, the gamma function and the Mittag-Leffler functions. After editing the article, run

    lake exe leanify prepare tests/Fractional/article.tex --lean tests/Fractional/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `fractional`. -/
def Fractional.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["fractional"]

#leanify_article Fractional "article.tex" "fnv1a64:6c087bcfe41d012e" with Fractional.vocabulary
