import Leanify.Meta

/-! # `article.tex`, compiled

`Means.doc` is the compilation of `Means.source`, the contents of `article.tex`, by
`compileArticle Means.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare examples/Means/article.tex --lean examples/Means/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Means "article.tex" "fnv1a64:29224d17a948361b"
