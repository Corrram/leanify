import Leanify.Meta

/-! # `article.tex`, compiled

`Refuted.doc` is the compilation of `Refuted.source`, the contents of `article.tex`, by
`compileArticle Refuted.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/Refuted/article.tex --lean tests/Refuted/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Refuted "article.tex" "fnv1a64:c2779501372b9319"
