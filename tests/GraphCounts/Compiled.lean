import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `graphcounts`: edges of standard graphs, labelled graphs, spanning trees, chromatic polynomials, Turan graphs and the Ramsey bound. After editing the article, run

    lake exe leanify prepare tests/GraphCounts/article.tex --lean tests/GraphCounts/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `graphcounts`. -/
def GraphCounts.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["graphcounts"]

#leanify_article GraphCounts "article.tex" "fnv1a64:55cb914f11b59e66" with GraphCounts.vocabulary
