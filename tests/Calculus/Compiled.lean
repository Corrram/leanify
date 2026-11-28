import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of functions of several variables (`f:\mathbb R^2\to\mathbb R`,
`f(x,y)\coloneqq …`, curried) and of partial derivatives (`\partial_x f`,
`\partial_2 h`, `\frac{\partial f}{\partial y}`, `\Delta f`), and of second derivatives
and the product rule for functions bound with words of the fields `realfunctions` and
`calculus` (`be twice differentiable`, `be differentiable`). After editing the article, run

    lake exe leanify prepare tests/Calculus/article.tex --lean tests/Calculus/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `calculus`. -/
def Calculus.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "calculus"]

#leanify_article Calculus "article.tex" "fnv1a64:f34abe03cea3fefc" with Calculus.vocabulary
