import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `inventory`: lot-size costs, the economic order and production quantities, backorders, reorder points and the newsvendor model. After editing the article, run

    lake exe leanify prepare tests/Inventory/article.tex --lean tests/Inventory/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `inventory`. -/
def Inventory.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["inventory"]

#leanify_article Inventory "article.tex" "fnv1a64:e7e5d0277d70290c" with Inventory.vocabulary
