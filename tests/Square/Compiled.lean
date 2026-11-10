import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled

`Square.doc` is the compilation of `Square.source`, the contents of `article.tex`, by
`compileArticle Square.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/Square/article.tex --lean tests/Square/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Square "article.tex" "fnv1a64:c04f34646b686126" with Leanify.UnitSquare.withCore
