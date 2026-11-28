import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of recursive definitions: a sequence with a first value and a step (`Let $a_0\coloneqq 1$. For every integer $n\ge1$, set $a_n\coloneqq 2a_{n-1}+1$.`), a sequence and a function defined by cases that use the symbol being defined, and a family with two indices, defined in a definition environment for the results after it, whose step takes a maximum over earlier values. After editing the article, run

    lake exe leanify prepare tests/Recursion/article.tex --lean tests/Recursion/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core. -/
def Recursion.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select []

#leanify_article Recursion "article.tex" "fnv1a64:cca792f8e9b31906" with Recursion.vocabulary
