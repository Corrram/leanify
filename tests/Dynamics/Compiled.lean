import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `dynamics`: iterates of a map, orbits, fixed and periodic points, the least period and the Lyapunov exponent. After editing the article, run

    lake exe leanify prepare tests/Dynamics/article.tex --lean tests/Dynamics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions` and `dynamics`. -/
def Dynamics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "dynamics"]

#leanify_article Dynamics "article.tex" "fnv1a64:fe061b7445b4a479" with Dynamics.vocabulary
