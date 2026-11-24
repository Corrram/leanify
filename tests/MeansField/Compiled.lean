import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `means`: means of two numbers as notions with their domains (`We write $H(x,y)$ for the harmonic mean of $x$ and $y$.`). After editing the article, run

    lake exe leanify prepare tests/MeansField/article.tex --lean tests/MeansField/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `means`. -/
def MeansField.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["means"]

#leanify_article MeansField "article.tex" "fnv1a64:c13c8d29ecba93af" with MeansField.vocabulary
