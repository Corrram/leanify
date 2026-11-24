import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `asymptotics`: comparisons of two functions at infinity as modifiers with a function (`$f$ is negligible compared to $g$`), conjoined hypotheses of `if`, regular variation and the limit at infinity as a description. After editing the article, run

    lake exe leanify prepare tests/Asymptotics/article.tex --lean tests/Asymptotics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `asymptotics`. -/
def Asymptotics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "asymptotics"]

#leanify_article Asymptotics "article.tex" "fnv1a64:bbe700018a51f4b2" with Asymptotics.vocabulary
