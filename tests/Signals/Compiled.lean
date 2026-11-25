import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `signals`: the normalized sinc, rectangular, triangular and unit step functions, Gaussian pulses, the Nyquist rate, decibels and first-order filters. After editing the article, run

    lake exe leanify prepare tests/Signals/article.tex --lean tests/Signals/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `signals`. -/
def Signals.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["signals"]

#leanify_article Signals "article.tex" "fnv1a64:827800b872cb308e" with Signals.vocabulary
