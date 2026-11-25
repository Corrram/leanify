import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `quantum`: energy levels of a particle in a box, a harmonic oscillator and the hydrogen atom, densities in a box, de Broglie wavelengths, photons, Rydberg's formula and the Compton shift. After editing the article, run

    lake exe leanify prepare tests/Quantum/article.tex --lean tests/Quantum/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `quantum`. -/
def Quantum.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["quantum"]

#leanify_article Quantum "article.tex" "fnv1a64:9a1b19e6a2f089cb" with Quantum.vocabulary
