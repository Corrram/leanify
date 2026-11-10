import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled

`TailDependence.doc` is the compilation of `TailDependence.source`, the contents of `article.tex`, by
`compileArticle TailDependence.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/TailDependence/article.tex --lean tests/TailDependence/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article TailDependence "article.tex" "fnv1a64:a371a18c59570205" with Leanify.UnitSquare.withCore
