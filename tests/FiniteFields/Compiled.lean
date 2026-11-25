import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `finitefields`: prime powers, general and special linear groups, matrices, subspaces and projective points over finite fields, and primitive elements. After editing the article, run

    lake exe leanify prepare tests/FiniteFields/article.tex --lean tests/FiniteFields/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `finitefields`. -/
def FiniteFields.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["finitefields"]

#leanify_article FiniteFields "article.tex" "fnv1a64:2b3ea8b7ec268733" with FiniteFields.vocabulary
