import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `transforms`: the Laplace, Mellin and Stieltjes transforms, convolution and autocorrelation, each defined where its integrand is integrable. After editing the article, run

    lake exe leanify prepare tests/Transforms/article.tex --lean tests/Transforms/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `transforms`. -/
def Transforms.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "transforms"]

#leanify_article Transforms "article.tex" "fnv1a64:1539f08c4a0e6989" with Transforms.vocabulary
