import Leanify.Meta
import Leanify.Library.Markov

/-! # `article.tex`, compiled

A test of the fields `hilbert` and `markov`: functions in `L^2` and `L^2_0`, inner products,
norms, operators and their powers, the Markov operator of a copula, Borel measurable maps of
the square and statistics of the first observations. After editing the article, run

    lake exe leanify prepare tests/Operators/article.tex --lean tests/Operators/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Operators "article.tex" "fnv1a64:4ba24c2d0bd123df" with Leanify.Markov.withCore
