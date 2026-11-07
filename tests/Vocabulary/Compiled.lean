import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled by the kernel

A test of the article's own notation (`We write …`), of its conventions (`By a
distribution we mean …`, `Throughout, increasing means …`) and of a field of the
vocabulary (`distributions`): `Vocabulary.compiled : compileArticle
Vocabulary.vocab Vocabulary.source = some Vocabulary.doc` is checked by the kernel
from the contents of `article.tex`. After editing the article, run

    lake exe leanify prepare tests/Vocabulary/article.tex --lean tests/Vocabulary/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `distributions`. -/
def Vocabulary.vocabulary : Leanify.Vocab := Leanify.Fields.select ["distributions"]

#leanify_article Vocabulary "article.tex" "fnv1a64:bbc98f68a9155036" with Vocabulary.vocabulary
