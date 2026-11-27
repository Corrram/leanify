import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `recurrences`: arithmetic and geometric progressions and their sums, solutions of the Fibonacci and of a linear recurrence (`$a$ is a solution of the Fibonacci recurrence`, a modifier whose phrase goes on after `of the`), characteristic roots. After editing the article, run

    lake exe leanify prepare tests/Recurrences/article.tex --lean tests/Recurrences/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `recurrences`. -/
def Recurrences.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["recurrences"]

#leanify_article Recurrences "article.tex" "fnv1a64:e529596ab8d84226" with Recurrences.vocabulary
