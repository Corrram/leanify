import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `traffic`: the Greenshields speed and flow, capacity, critical density, uncongested speed, headway and spacing. After editing the article, run

    lake exe leanify prepare tests/Traffic/article.tex --lean tests/Traffic/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `traffic`. -/
def Traffic.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["traffic"]

#leanify_article Traffic "article.tex" "fnv1a64:e598bb36b26d962c" with Traffic.vocabulary
