import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled

A test of a revised article: changes marked by a conditional of the article (`\newif`,
`\color`, margin notes), definitions in the sentences of a running text (`The copulas …
describe …`, `we write … for the transpose of $C$`, `the function $\Phi:A\to B$ given by`), and
decorations with a star (`C_{1}^{*}`).

`Revision.doc` is the compilation of `Revision.source`, the contents of `article.tex`, by
`compileArticle Revision.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/Revision/article.tex --lean tests/Revision/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Revision "article.tex" "fnv1a64:4adf263e2e5265de" with Leanify.UnitSquare.withCore
