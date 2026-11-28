import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of pairs and of sums over finite sets: sums and products over the elements of a finite set of real numbers (`\sum_{x\in A} e`), a pair in a set of pairs (`(a,b)\in A\times B`, `a set $K$ of pairs of integers`, `for all $(x,y)\in K$`), a notation for a relation between pairs with several conditions (`We write $(A,B)\preceq(C,D)$ if … and ….`), objects that exist on a set of the result (`there exists a function $w\colon V\to\mathbb{R}$ such that …`), and connectives in parentheses. After editing the article, run

    lake exe leanify prepare tests/Pairs/article.tex --lean tests/Pairs/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `realsets`. -/
def Pairs.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realsets"]

#leanify_article Pairs "article.tex" "fnv1a64:8b1ee8b4fff82c81" with Pairs.vocabulary
