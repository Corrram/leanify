import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `structures` (named `groups`): groups as sets of their elements, named finite groups, a modifier whose argument is a group (`isomorphic to $C_4$`), `Every NP $x$ is ADJ`, and clauses joined by `or` and by `if and only if`. After editing the article, run

    lake exe leanify prepare tests/Groups/article.tex --lean tests/Groups/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `groups`. -/
def Groups.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["groups"]

#leanify_article Groups "article.tex" "fnv1a64:801f520b3471d241" with Groups.vocabulary
