import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `realsets` of the vocabulary: sets of real numbers bound by a noun (`a nonempty compact set $S$`, `every open subset $U$ of $\mathbb{R}$`), adjectives of the core language and of the field in one list, a modifier after its noun (`a set of measure zero`), and `if and only if` between clauses. After editing the article, run

    lake exe leanify prepare tests/Topology/article.tex --lean tests/Topology/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `realsets`. -/
def Topology.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realsets"]

#leanify_article Topology "article.tex" "fnv1a64:98fcd1e08428daf8" with Topology.vocabulary
