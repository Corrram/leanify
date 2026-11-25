import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `collatz`: the Collatz map and its iterates, total stopping times, stopping times and the highest points of trajectories. After editing the article, run

    lake exe leanify prepare tests/Collatz/article.tex --lean tests/Collatz/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `collatz`. -/
def Collatz.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["collatz"]

#leanify_article Collatz "article.tex" "fnv1a64:26c0ce7370954046" with Collatz.vocabulary
