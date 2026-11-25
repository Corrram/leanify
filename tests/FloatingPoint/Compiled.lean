import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `floatingpoint`: machine epsilon, unit roundoff, the range of a floating-point system, absolute and relative errors, rounding and representable numbers. After editing the article, run

    lake exe leanify prepare tests/FloatingPoint/article.tex --lean tests/FloatingPoint/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `floatingpoint`. -/
def FloatingPoint.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["floatingpoint"]

#leanify_article FloatingPoint "article.tex" "fnv1a64:fa4801ed9f954f1a" with FloatingPoint.vocabulary
