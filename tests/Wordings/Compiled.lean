import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled

A test of the freer wordings of a research article with the field `unitsquare`: a
definition inside a sentence of prose (named by the words before it, or by `denotes the …`
after it), a displayed formula `f(C)=…` that defines the named symbol `f`, definitions after
a colon and after `, where`, a definition about a letter that an earlier definition
introduced (`For a copula $C$, …`), the consequences after `, a normalization that makes`,
the set `$\Gamma$ of all such couplings`, a statement about a random pair that `follows the
coupling associated with` a copula, `depend affinely on`, values `attained only by` an
object and by `its survival copula`, the maximizers of a map over a class, and steps of a
proof about a letter that the proof introduces in words.

`Wordings.doc` is the compilation of `Wordings.source`, the contents of `article.tex`, by
`compileArticle Wordings.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/Wordings/article.tex --lean tests/Wordings/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Wordings "article.tex" "fnv1a64:64d04d495d4b060e" with Leanify.UnitSquare.withCore
