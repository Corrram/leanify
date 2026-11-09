import Leanify.Meta

/-! # `article.tex`, compiled

A test of functions of several variables (`f:\mathbb R^2\to\mathbb R`,
`f(x,y)\coloneqq …`, curried) and of partial derivatives (`\partial_x f`,
`\partial_2 h`, `\frac{\partial f}{\partial y}`, `\Delta f`). After editing the
article, run

    lake exe leanify prepare tests/Calculus/article.tex --lean tests/Calculus/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Calculus "article.tex" "fnv1a64:970d7db921e44b5b"
