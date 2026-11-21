import Leanify.Meta

/-! # `article.tex`, compiled

`Assumed.doc` is the compilation of `Assumed.source`, the contents of `article.tex`, by
`compileArticle Assumed.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare article.tex --lean ./Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Assumed "article.tex" "fnv1a64:70d625fc593f4c2d"
