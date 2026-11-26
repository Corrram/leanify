import Leanify.Denote
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # The meaning of the field `randomvariables`

A random variable is a real function of the outcome `ω` of one probability space for the
whole article: `[0,1]` with Lebesgue measure. Every joint distribution of finitely or
countably many real random variables is the distribution of functions on this space, so a
statement about the distributions of the random variables of an article (their
expectations, variances, probabilities, independence) means the same on it as on any
other probability space that carries them. -/

namespace Leanify.RandomVariables

/-- A random variable: a function of the outcome `ω ∈ [0,1]` (its values elsewhere are not
used). -/
def RV : Type := ℝ → ℝ

/-- The random variable `0`. -/
def RV.zero : RV := fun _ => 0

/-- `X(ω)`, the value of `X` at the outcome `ω`. -/
def eval (X : RV) (ω : ℝ) : ℝ := X ω

/-- `X` is a random variable: a (Borel) measurable function of the outcome. -/
def IsRV (X : RV) : Prop := Measurable (fun ω : ℝ => X ω)

end Leanify.RandomVariables
