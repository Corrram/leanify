import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the fields `numbers`, `torus`, `hyperbolic` and `trigonometry` of the
vocabulary (a field of symbols with domains: `\arcsin` on `[-1,1]`), of generic
constants (`Throughout, $C_m$ denotes …`: for every `m` there is `C_m`), of
existence and uniqueness (`there is exactly one NP`) and of a phrase with two
meanings (`natural number`, refused). After editing the article, run

    lake exe leanify prepare tests/Fields/article.tex --lean tests/Fields/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `numbers`, `torus`,
`hyperbolic` and `trigonometry`. -/
def Fields.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["numbers", "torus", "hyperbolic", "trigonometry"]

#leanify_article Fields "article.tex" "fnv1a64:13a2384b6a09c6f2" with Fields.vocabulary
