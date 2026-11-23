import Leanify.Denote
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # The meaning of the field `special`

The beta function, the zeta function on `(1, ∞)` and the Bernoulli numbers as real functions
(Leanify asks for positive arguments, `s > 1` and natural numbers, where they are used). -/

namespace Leanify.Special

/-- `B(x,y) = Γ(x)Γ(y)/Γ(x+y)`. -/
noncomputable def beta (x y : ℝ) : ℝ := Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)

/-- `ζ(s) = ∑_{n ≥ 1} n^{-s}` (for `s > 1`; it equals `riemannZeta s` there). -/
noncomputable def zeta (s : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s

/-- The `n`-th Bernoulli number, `B_1 = -1/2`. -/
noncomputable def bernoulli (n : ℝ) : ℝ := (_root_.bernoulli ⌊n⌋₊ : ℝ)

end Leanify.Special
