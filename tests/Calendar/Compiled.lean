import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `calendar`: leap years, days of years and months, Zeller's congruence and counts of leap years. After editing the article, run

    lake exe leanify prepare tests/Calendar/article.tex --lean tests/Calendar/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `calendar`. -/
def Calendar.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["calendar"]

#leanify_article Calendar "article.tex" "fnv1a64:120f0693f0ebbb6a" with Calendar.vocabulary
