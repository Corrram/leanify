import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the default vocabulary: an article that names no field is read with every field (`math`), here with words of `combinatorialgames`, `algorithms` and `relativity`. After editing the article, run

    lake exe leanify prepare tests/Default/article.tex --lean tests/Default/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: every field (`math`), the default. -/
def Default.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["math"]

#leanify_article Default "article.tex" "fnv1a64:e3f5cf49a523ca71" with Default.vocabulary
