import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `structures`: groups, rings, fields, vector spaces, topological spaces and
ordered sets with their elements, substructures named by a complement (`subgroup of $G$`),
and maps bound by their signatures (`$\varphi\colon G\to H$`). After editing the article, run

    lake exe leanify prepare tests/Structures/article.tex --lean tests/Structures/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `structures`. -/
def Structures.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["structures"]

#leanify_article Structures "article.tex" "fnv1a64:8e661c9fb7db3ff9" with Structures.vocabulary
