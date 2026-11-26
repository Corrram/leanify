import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `topologies`: topologies on `ℝ` as families of sets, adjectives of sets with a topology (`$\tau$-open`, `continuous from $\tau$ to $\sigma$`), and the named topologies. After editing the article, run

    lake exe leanify prepare tests/Topologies/article.tex --lean tests/Topologies/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realsets` and `topologies`. -/
def Topologies.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realsets", "topologies"]

#leanify_article Topologies "article.tex" "fnv1a64:ad3770afd596e87b" with Topologies.vocabulary
