import Leanify.Denote
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # The meaning of the field `calculus`

Higher derivatives of a real function, for a natural number given as a real number. -/

namespace Leanify.Calculus

/-- The `⌊n⌋₊`th derivative of `f` (Mathlib `iteratedDeriv`). -/
noncomputable def nthDeriv (n : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := iteratedDeriv ⌊n⌋₊ f

/-- `f` is `⌊n⌋₊` times continuously differentiable (Mathlib `ContDiff ℝ n`). -/
def TimesContDiff (n : ℝ) (f : ℝ → ℝ) : Prop := ContDiff ℝ ⌊n⌋₊ f

/-- `f` is `⌊n⌋₊` times differentiable: its derivatives of order `k < ⌊n⌋₊` are
differentiable. -/
def TimesDiff (n : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, k < ⌊n⌋₊ → Differentiable ℝ (iteratedDeriv k f)

end Leanify.Calculus
