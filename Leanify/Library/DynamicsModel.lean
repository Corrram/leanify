import Leanify.Denote
import Mathlib.Logic.Function.Iterate

/-! # The meaning of the field `dynamics`

The iterates of a real function, for a natural number given as a real number. -/

namespace Leanify.Dynamics

/-- `f ∘ … ∘ f`, `⌊n⌋₊` times (the identity for `n < 1`). -/
noncomputable def iterate (n : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := f^[⌊n⌋₊]

end Leanify.Dynamics
