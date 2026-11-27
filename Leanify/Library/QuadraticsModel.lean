import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Leanify.Denote

/-! # The meaning of the field `quadratics`

The roots of the quadratic `ax² + bx + c` as a polynomial over `ℂ` (Mathlib `Polynomial.roots`,
with multiplicity): their sum and their product as real numbers, where they are real. -/

namespace Leanify.Quadratics

noncomputable section
open Polynomial

/-- The quadratic `ax² + bx + c` as a polynomial over `ℂ`. -/
def quadC (a b c : ℝ) : ℂ[X] := C (a : ℂ) * X ^ 2 + C (b : ℂ) * X + C (c : ℂ)

/-- The sum of the complex roots of the quadratic (with multiplicity) is a real number. -/
def RootSumReal (a b c : ℝ) : Prop := ∃ s : ℝ, (s : ℂ) = (quadC a b c).roots.sum

/-- The product of the complex roots of the quadratic (with multiplicity) is a real number. -/
def RootProdReal (a b c : ℝ) : Prop := ∃ s : ℝ, (s : ℂ) = (quadC a b c).roots.prod

/-- The sum of the roots of the quadratic: the real number that is the sum of its complex roots
(`0` where it is not real). -/
def rootSum (a b c : ℝ) : ℝ := by
  classical exact if h : RootSumReal a b c then Classical.choose h else 0

/-- The product of the roots of the quadratic: the real number that is the product of its complex
roots (`0` where it is not real). -/
def rootProd (a b c : ℝ) : ℝ := by
  classical exact if h : RootProdReal a b c then Classical.choose h else 0

end

end Leanify.Quadratics
