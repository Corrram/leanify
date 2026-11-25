import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `music`: piano key frequencies, semitones, cents, commas, equal temperaments and MIDI numbers. After editing the article, run

    lake exe leanify prepare tests/Music/article.tex --lean tests/Music/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `music`. -/
def Music.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["music"]

#leanify_article Music "article.tex" "fnv1a64:2766024f0e36679f" with Music.vocabulary
