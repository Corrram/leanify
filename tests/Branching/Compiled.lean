import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `branching` with `distributions`: offspring means and generating functions, subcritical, critical and supercritical offspring distributions, expected generation sizes and extinction probabilities. After editing the article, run

    lake exe leanify prepare tests/Branching/article.tex --lean tests/Branching/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `branching` and `distributions`. -/
def Branching.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["branching", "distributions"]

#leanify_article Branching "article.tex" "fnv1a64:b1a7bc4e956af30d" with Branching.vocabulary
