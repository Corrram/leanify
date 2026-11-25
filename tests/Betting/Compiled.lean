import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `betting`: implied probabilities, fair odds, odds in favour, expected profits, the Kelly criterion, logarithmic growth and bookmaker margins. After editing the article, run

    lake exe leanify prepare tests/Betting/article.tex --lean tests/Betting/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `betting`. -/
def Betting.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["betting"]

#leanify_article Betting "article.tex" "fnv1a64:e3687091a1c9626e" with Betting.vocabulary
