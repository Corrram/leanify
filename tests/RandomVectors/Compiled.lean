import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `randomvectors`: random vectors bound by a noun with their dimension, their sums and multiples, equality in distribution (`X\stackrel{d}{=}Y`, `\overset{\mathcal{D}}{=}`, `identically distributed`), independence, integrability and the means of the coordinates, a vector added to a random vector and a matrix applied to one (`AX+b`), characteristic functions (named by the article from the notion), `X\\sim F` for a distribution function and the mean vector, notions that the article defines by them, and notes above a relation that are labels or reasons. After editing the article, run

    lake exe leanify prepare tests/RandomVectors/article.tex --lean tests/RandomVectors/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `randomvectors` and `linearsystems`. -/
def RandomVectors.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["randomvectors", "linearsystems"]

#leanify_article RandomVectors "article.tex" "fnv1a64:0fc0dc7e93fa1de8" with RandomVectors.vocabulary
