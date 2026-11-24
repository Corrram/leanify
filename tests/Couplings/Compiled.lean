import Leanify.Meta
import Leanify.Library.UnitSquare

/-! # `article.tex`, compiled

A test of couplings and random pairs with the field `unitsquare`: the class of couplings,
expectations `\mathbb{E}_\gamma[…]` of the two coordinates, the coupling of a copula and the
copula of a coupling, families of copulas from maps of the interval, equality cases (`with
equality if and only if`, `… if and only if $C=A_1$`), sets of pairs of points, and the two
random variables of a result as a random pair with its joint law.

`Couplings.doc` is the compilation of `Couplings.source`, the contents of `article.tex`, by
`compileArticle Couplings.vocab` (`leanify audit` has the kernel evaluate it). The last
string pins those contents: after editing the article, run

    lake exe leanify prepare tests/Couplings/article.tex --lean tests/Couplings/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Couplings "article.tex" "fnv1a64:71a0ca9dcbb17e97" with Leanify.UnitSquare.withCore
