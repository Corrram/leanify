import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled by the kernel

A test of conventions about constants (`may depend on`, `uniform in`, `independent
of`) and of the order of quantifiers they give, of multi-indices (`\partial^I f`), of
quantities set for every value of a parameter (`For a positive integer $j$, we set
…`), and of classes of functions and of families defined by bounds. After editing
the article, run

    lake exe leanify prepare tests/Conventions/article.tex --lean tests/Conventions/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `numbers`. -/
def Conventions.vocabulary : Leanify.Vocab := Leanify.Fields.select ["numbers"]

#leanify_article Conventions "article.tex" "fnv1a64:db0f5f29963f7962" with Conventions.vocabulary
