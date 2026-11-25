import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `circuits`: series and parallel resistances, power, RC time constants and charging, stored energies, LC resonance, RLC impedance and quality factors. After editing the article, run

    lake exe leanify prepare tests/Circuits/article.tex --lean tests/Circuits/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `circuits`. -/
def Circuits.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["circuits"]

#leanify_article Circuits "article.tex" "fnv1a64:b1d7d27e041217e6" with Circuits.vocabulary
