import Leanify.Meta

/-! # `article.tex`, compiled

A test of proof sentences that give their reasons in words, restate an informal sentence
(`INFORMAL, that is, FORMAL`) or choose an object (`Let $c>0$ be such that …`, `we can find
… such that …`, `we obtain a NP $X$ such that …`). After editing the article, run

    lake exe leanify prepare tests/Steps/article.tex --lean tests/Steps/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Steps "article.tex" "fnv1a64:2c5e073f0e2ba4b6"
