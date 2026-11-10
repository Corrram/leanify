import Leanify.Meta

/-! # `article.tex`, compiled

A test of notions that an article uses without defining them: the nouns and adjectives
that its preamble declares (`\usepackage[notions={graph, finite graph}]{leanify}`), the
words that name numbers (`quantities={degree}`), the symbols that a sentence introduces
for quantities that the article does not define (`Let $\chi(G)$ denote the chromatic
number of a graph $G$.`), and the results that it quotes from the literature (a heading
that cites its source, and no proof). `Undefined.vocab` is the core vocabulary with the
notions of the preamble (`Undefined.declared`), and the audit proves that these are the
notions of the source (`Undefined.declaredNotions`). The article is certified: the
theorem is derived from the two quoted lemmas, which are the axioms
`Undefined.Quoted.claim0` and `Undefined.Quoted.claim1` of the certificate. After editing
the article, run

    lake exe leanify prepare tests/Undefined/article.tex --lean tests/Undefined/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Undefined "article.tex" "fnv1a64:fa4c182ba35dd46d"
