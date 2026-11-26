import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the notions that an article defines in sentences that are not read
(`A metric space is \emph{homogeneous} if …`, `A \emph{Kripke frame} is …`): each is an adjective or a
noun without a meaning in Lean, and what the article states about them is read. After editing the article, run

    lake exe leanify prepare tests/Defined/article.tex --lean tests/Defined/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `structures`. -/
def Defined.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["structures"]

#leanify_article Defined "article.tex" "fnv1a64:88b93b4fc5dcc95f" with Defined.vocabulary
