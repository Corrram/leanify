import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `kinematics`: constant acceleration, stopping distances, circular motion and elastic and inelastic collisions. After editing the article, run

    lake exe leanify prepare tests/Kinematics/article.tex --lean tests/Kinematics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `kinematics`. -/
def Kinematics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["kinematics"]

#leanify_article Kinematics "article.tex" "fnv1a64:73db5a0c08cebc4c" with Kinematics.vocabulary
