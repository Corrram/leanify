import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `games`: values, lower and upper values, optimal strategies and expected payoffs of two-by-two zero-sum games. After editing the article, run

    lake exe leanify prepare tests/Games/article.tex --lean tests/Games/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `games`. -/
def Games.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["games"]

#leanify_article Games "article.tex" "fnv1a64:4faf0bcad52522d0" with Games.vocabulary
