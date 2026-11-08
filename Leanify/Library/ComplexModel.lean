import Leanify.Library.Complex
import Leanify.Denote
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The meaning of the complex numbers

`Complex.model` interprets the base type of `Complex.vocab` as Mathlib's `ℂ` and its
constants as Mathlib's operations. -/

namespace Leanify.Complex

/-- `z^r` for a natural number `r` (Leanify asks that `r ∈ ℕ`). -/
noncomputable def powNat (z : ℂ) (r : ℝ) : ℂ := z ^ ⌊r⌋₊

/-- `∑_{k=a}^{b} f(k)` over the integers `k` with `a ≤ k ≤ b`. -/
noncomputable def finSum (a b : ℝ) (f : ℝ → ℂ) : ℂ :=
  Finset.sum (Finset.Icc ⌈a⌉ ⌊b⌋) fun k : ℤ => f k

/-- `∏_{k=a}^{b} f(k)` over the integers `k` with `a ≤ k ≤ b`. -/
noncomputable def finProd (a b : ℝ) (f : ℝ → ℂ) : ℂ :=
  Finset.prod (Finset.Icc ⌈a⌉ ⌊b⌋) fun k : ℤ => f k

/-- The model of `Complex.vocab`: its base type is `ℂ`. -/
noncomputable def model : Model where
  base := fun _ => ℂ
  default := fun _ => 0
  consts := [
    ⟨.real ⟶ C, fun x : ℝ => (x : ℂ)⟩,
    ⟨C ⟶ C ⟶ C, fun z w : ℂ => z + w⟩,
    ⟨C ⟶ C ⟶ C, fun z w : ℂ => z - w⟩,
    ⟨C ⟶ C ⟶ C, fun z w : ℂ => z * w⟩,
    ⟨C ⟶ C ⟶ C, fun z w : ℂ => z / w⟩,
    ⟨C ⟶ C, fun z : ℂ => -z⟩,
    ⟨C ⟶ .real ⟶ C, powNat⟩,
    ⟨C ⟶ .real, fun z : ℂ => ‖z‖⟩,
    ⟨C ⟶ C, fun z : ℂ => (starRingEnd ℂ) z⟩,
    ⟨C ⟶ .real, fun z : ℂ => z.re⟩,
    ⟨C ⟶ .real, fun z : ℂ => z.im⟩,
    ⟨C ⟶ C, _root_.Complex.exp⟩,
    ⟨C, _root_.Complex.I⟩,
    ⟨.real ⟶ .real ⟶ (.real ⟶ C) ⟶ C, finSum⟩,
    ⟨.real ⟶ .real ⟶ (.real ⟶ C) ⟶ C, finProd⟩]

end Leanify.Complex
