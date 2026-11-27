import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `words`: words, palindromes, words without equal adjacent letters, Fibonacci words, necklaces and de Bruijn sequences. After editing the article, run

    lake exe leanify prepare tests/Words/article.tex --lean tests/Words/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `words`. -/
def Words.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["words"]

#leanify_article Words "article.tex" "fnv1a64:88fc7d805142cf13" with Words.vocabulary
