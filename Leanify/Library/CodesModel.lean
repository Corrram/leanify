import Mathlib.InformationTheory.Hamming
import Mathlib.SetTheory.Cardinal.Finite
import Leanify.Denote

/-! # The meaning of the field `codes`

The volume of the Hamming ball: the number of binary words of length `n` within Hamming
distance `r` of one of them (Mathlib `hammingDist`), the all-zero word. Its formula
`∑_{i=0}^{r} \binom{n}{i}` is a theorem, not the definition. -/

namespace Leanify.Codes

noncomputable section

/-- The volume of the Hamming ball of radius `r` in dimension `n`. -/
def hammingBall (r n : ℝ) : ℝ :=
  (Nat.card {w : Fin ⌊n⌋₊ → Bool // hammingDist w (fun _ => false) ≤ ⌊r⌋₊} : ℝ)

end

end Leanify.Codes
