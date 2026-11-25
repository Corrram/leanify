import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `ratings`: Elo scores and updates, Bradley-Terry and logistic win probabilities and the Pythagorean expectation. After editing the article, run

    lake exe leanify prepare tests/Ratings/article.tex --lean tests/Ratings/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `ratings`. -/
def Ratings.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["ratings"]

#leanify_article Ratings "article.tex" "fnv1a64:5b10adf816ef46be" with Ratings.vocabulary
