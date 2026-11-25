import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `codes`: binary words, Hamming weight and distance, Hamming balls, the sphere-packing, Singleton and Gilbert-Varshamov bounds and the rate. After editing the article, run

    lake exe leanify prepare tests/Codes/article.tex --lean tests/Codes/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `codes`. -/
def Codes.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["codes"]

#leanify_article Codes "article.tex" "fnv1a64:e65a367a8abe61c4" with Codes.vocabulary
