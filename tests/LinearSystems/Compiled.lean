import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `linearsystems`: a matrix applied to a vector (`Qy`, `Q(2y)`), matrices and vectors bound by their sets (`Q\in\mathbb{R}^{n\times\ell}`, `b\in\mathbb{R}^\ell`, `x\in\mathbb{R}_{\ge 0}^n`), the order of vectors in every coordinate (`x\le y`, `x\ge 0`), `x^\top y` for the inner product, and Farkas's lemma as `exactly one of the following two assertions holds:` with two existence statements. After editing the article, run

    lake exe leanify prepare tests/LinearSystems/article.tex --lean tests/LinearSystems/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `linearsystems`. -/
def LinearSystems.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["linearsystems"]

#leanify_article LinearSystems "article.tex" "fnv1a64:fae14abceab155a8" with LinearSystems.vocabulary
