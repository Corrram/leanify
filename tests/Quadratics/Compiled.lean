import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `quadratics`: discriminants, roots, Vieta's sums and products, vertices and extreme values of quadratics, and the discriminant and Cardano root of cubics. After editing the article, run

    lake exe leanify prepare tests/Quadratics/article.tex --lean tests/Quadratics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `quadratics`. -/
def Quadratics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["quadratics"]

#leanify_article Quadratics "article.tex" "fnv1a64:dc99e76bada19ff6" with Quadratics.vocabulary
