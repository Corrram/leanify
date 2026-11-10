import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the language of proofs: assumptions (`Assume that …`, `Suppose …`), which
are hypotheses of the following sentences of their result or proof and add up; `Assume
further that …`, which belongs to the assumption before it; `Assume now that …`, which
takes its place; `Without loss of generality, assume …`; cases written as the items of
a list, whose headings are hypotheses of their items; hypotheses made for contradiction
and the contradiction that ends them; and inductions, with `the statement holds for
$n$`, `for $n-1$`, `for $n+1$` and `for all $m<n$`. The article is certified: every
step is closed by the standard tactic, under hypotheses that are shown to hold together.
After editing
the article, run

    lake exe leanify prepare tests/Arguments/article.tex --lean tests/Arguments/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `numbers`. -/
def Arguments.vocabulary : Leanify.Vocab := Leanify.Fields.select ["numbers"]

#leanify_article Arguments "article.tex" "fnv1a64:6e51d55449713d7e" with Arguments.vocabulary
