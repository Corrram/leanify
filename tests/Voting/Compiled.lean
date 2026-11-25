import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `voting`: Hare, Droop and majority quotas, D'Hondt and Webster quotients, pairwise contests and Borda scores. After editing the article, run

    lake exe leanify prepare tests/Voting/article.tex --lean tests/Voting/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `voting`. -/
def Voting.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["voting"]

#leanify_article Voting "article.tex" "fnv1a64:fab5e68f2cb67942" with Voting.vocabulary
