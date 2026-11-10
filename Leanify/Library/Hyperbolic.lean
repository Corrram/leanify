import Leanify.Vocab

/-! # Vocabulary: hyperbolic functions

`\sinh`, `\cosh` and `\tanh` of a real number. The field is data alone: each symbol is a
constant whose Lean meaning is a declaration of Mathlib, named in `constLean`. Nothing
else says what the symbols mean, and no Lean code is written for the field: a new field
of this kind is a list of symbols, types and names. -/

namespace Leanify.Hyperbolic

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\sinh", w!"\\cosh", w!"\\tanh"]
  constLean := [w!"Real.sinh", w!"Real.cosh", w!"Real.tanh"]
  modules := [w!"Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"]
  symbols := [
    { sym := w!"\\sinh", ty := .real ⟶ .real, const := some 0,
      doc := "the hyperbolic sine (Mathlib `Real.sinh`)" },
    { sym := w!"\\cosh", ty := .real ⟶ .real, const := some 1,
      doc := "the hyperbolic cosine (Mathlib `Real.cosh`)" },
    { sym := w!"\\tanh", ty := .real ⟶ .real, const := some 2,
      doc := "the hyperbolic tangent (Mathlib `Real.tanh`)" }]

end Leanify.Hyperbolic
