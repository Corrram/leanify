import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled

`Notions.doc` is the compilation of `Notions.source`, the contents of `article.tex`, by
`compileArticle Notions.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/Notions/article.tex --lean tests/Notions/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Notions "article.tex" "fnv1a64:cb22fadc61afdbae" with Leanify.UnitSquare.withCore
