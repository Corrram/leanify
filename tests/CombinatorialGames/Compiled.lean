import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `combinatorialgames`: nim-sums, winning moves of Nim, Grundy values of subtraction games and Wythoff pairs. After editing the article, run

    lake exe leanify prepare tests/CombinatorialGames/article.tex --lean tests/CombinatorialGames/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `combinatorialgames`. -/
def CombinatorialGames.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["combinatorialgames"]

#leanify_article CombinatorialGames "article.tex" "fnv1a64:30bcadb83608fb8c" with CombinatorialGames.vocabulary
