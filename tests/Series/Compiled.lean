import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `series`: summable and absolutely summable sequences, sums of series and power series, the radius of convergence, the limits of a sequence. After editing the article, run

    lake exe leanify prepare tests/Series/article.tex --lean tests/Series/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `series`. -/
def Series.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "series"]

#leanify_article Series "article.tex" "fnv1a64:2d0fdeea5adf0ca5" with Series.vocabulary
