import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `designs`: replication numbers and blocks of 2-designs, Steiner triple systems and projective and affine planes. After editing the article, run

    lake exe leanify prepare tests/Designs/article.tex --lean tests/Designs/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `designs`. -/
def Designs.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["designs"]

#leanify_article Designs "article.tex" "fnv1a64:654a1917dcd35247" with Designs.vocabulary
