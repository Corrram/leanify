import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `learning`: activation functions, cross-entropy and hinge losses, precision, recall, F1, accuracy and the Matthews correlation. After editing the article, run

    lake exe leanify prepare tests/Learning/article.tex --lean tests/Learning/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `learning`. -/
def Learning.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["learning"]

#leanify_article Learning "article.tex" "fnv1a64:1568f43902980816" with Learning.vocabulary
