import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled by the kernel

`TailDependence.compiled : compileArticle TailDependence.vocab TailDependence.source = some TailDependence.doc` is checked
by the kernel from the contents of `article.tex`. The last string pins those contents:
after editing the article, run

    lake exe leanify prepare tests/TailDependence/article.tex --lean tests/TailDependence/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article TailDependence "article.tex" "fnv1a64:a371a18c59570205" with Leanify.UnitSquare.withCore
