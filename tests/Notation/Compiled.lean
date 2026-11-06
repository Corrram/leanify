import Leanify.Meta

/-! # `article.tex`, compiled by the kernel

A test of the notation beyond the core grammar (composition, inclusion, suprema,
finite sums, equivalent statements): `Notation.compiled : compileArticle
Notation.vocab Notation.source = some Notation.doc` is checked by the kernel from
the contents of `article.tex`. After editing the article, run

    lake exe leanify prepare tests/Notation/article.tex --lean tests/Notation/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Notation "article.tex" "fnv1a64:7440571e6b3cae8b"
