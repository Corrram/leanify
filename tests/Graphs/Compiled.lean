import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `graphs` of the vocabulary: a type of its own, modifiers with an argument (`a graph $G$ on $n$ vertices`, `a $k$-regular graph`), notions of a vertex and a graph, and the complement `\overline{G}` as a decoration. After editing the article, run

    lake exe leanify prepare tests/Graphs/article.tex --lean tests/Graphs/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `graphs`. -/
def Graphs.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["graphs"]

#leanify_article Graphs "article.tex" "fnv1a64:16a7d6d6bdc91624" with Graphs.vocabulary
