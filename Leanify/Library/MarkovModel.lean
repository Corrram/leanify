import Leanify.Library.Markov
import Leanify.Library.HilbertModel

/-! # The meaning of the vocabulary of Markov operators

The Markov operator of a copula `C`: `(T_Cg)(u) = ∫ g(y) K_C(u,\mathrm{d}y)`, with Mathlib's
conditional kernel `K_C = (measureOf C).condKernel` of the probability measure of `C` on
`[0,1]^2` (the conditional distribution of the second coordinate given the first). It is
`\mathbb{E}[g(V)\mid U=u]` for `(U,V)` with the distribution function `C`, defined at every
point `u` (a version of the conditional expectation). -/

namespace Leanify.Markov.Model
open MeasureTheory UnitSquare
open scoped unitInterval

/-- The Markov operator of a copula. -/
noncomputable def markovOp (C : I → I → ℝ) (g : I → ℝ) : I → ℝ :=
  fun u => ∫ y, g y ∂((measureOf C).condKernel u)

end Leanify.Markov.Model
