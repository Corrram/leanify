import Leanify.Meta

/-! # `article.tex`, compiled

`Demo.doc` is the compilation of `Demo.source`, the contents of `article.tex`, by
`compileArticle Demo.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare examples/Demo/article.tex --lean examples/Demo/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Demo "article.tex" "fnv1a64:710f4157caa9adce"
