import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled by the kernel

A test of the language of proofs: assumptions (`Assume that …`, `Suppose …`, `Assume
further that …`), which are hypotheses of the following sentences of their result or
proof; cases written as the items of a list, whose headings are hypotheses of their
items; hypotheses made for contradiction and the contradiction that ends them; the
hypothesis of an induction; and what is not read, because the text does not say where
a hypothesis ends or which statement it is. After editing
the article, run

    lake exe leanify prepare tests/Arguments/article.tex --lean tests/Arguments/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `numbers`. -/
def Arguments.vocabulary : Leanify.Vocab := Leanify.Fields.select ["numbers"]

#leanify_article Arguments "article.tex" "fnv1a64:afc37e18dfc5ee46" with Arguments.vocabulary
