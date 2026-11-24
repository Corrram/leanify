import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `convexity`: log-convex, harmonically convex, GA-convex, s-convex, h-convex, P-functions, Godunova-Levin and Wright-convex functions, integral means and the Hermite-Hadamard gap. After editing the article, run

    lake exe leanify prepare tests/Convexity/article.tex --lean tests/Convexity/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `convexity`. -/
def Convexity.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["convexity"]

#leanify_article Convexity "article.tex" "fnv1a64:e365da45e3a0eb40" with Convexity.vocabulary
