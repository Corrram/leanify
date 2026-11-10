import Leanify.Library.Build

/-! # Vocabulary: inverse trigonometric functions and the cotangent

`\arcsin`, `\arccos`, `\arctan` and `\cot` of a real number (`\sin`, `\cos` and `\tan`
are in the core). The field is data alone: each symbol is a constant whose Lean meaning
is a declaration of Mathlib, named in `constLean`.

Three of the four have a domain: `\arcsin` and `\arccos` on `[-1,1]`, `\cot` where the
sine is not zero. Mathlib's functions have values outside (`Real.arcsin 2 = π/2`,
`Real.cot 0 = 0`); the domain of the symbol keeps an article from using them: a claim
about `\arcsin x` is meaningful only for `-1 ≤ x ≤ 1`. -/

namespace Leanify.Trigonometry
open Build

/-- `[-1,1]`. -/
def unitBall : Tm := predR fun x => and (le (neg (num 1)) x) (le x (num 1))
/-- Where the sine is not zero. -/
def sineNonzero : Tm := predR fun x => ne (app (lift (.prim (.realFn .sin))) x) (num 0)

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\arcsin", w!"\\arccos", w!"\\arctan", w!"\\cot"]
  constLean := [w!"Real.arcsin", w!"Real.arccos", w!"Real.arctan", w!"Real.cot"]
  modules := [w!"Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse",
    w!"Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan",
    w!"Mathlib.Analysis.Complex.Trigonometric"]
  symbols := [
    { sym := w!"\\arcsin", ty := .real ⟶ .real, const := some 0, doms := [some unitBall],
      doc := "the inverse sine, on `[-1,1]` (Mathlib `Real.arcsin`)" },
    { sym := w!"\\arccos", ty := .real ⟶ .real, const := some 1, doms := [some unitBall],
      doc := "the inverse cosine, on `[-1,1]` (Mathlib `Real.arccos`)" },
    { sym := w!"\\arctan", ty := .real ⟶ .real, const := some 2,
      doc := "the inverse tangent (Mathlib `Real.arctan`)" },
    { sym := w!"\\cot", ty := .real ⟶ .real, const := some 3, doms := [some sineNonzero],
      doc := "the cotangent, where the sine is not zero (Mathlib `Real.cot`)" }]

end Leanify.Trigonometry
