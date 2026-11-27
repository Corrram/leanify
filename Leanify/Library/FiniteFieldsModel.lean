import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Leanify.Denote

/-! # The meaning of the field `finitefields`

Counts over the field with `q` elements: Mathlib's `GaloisField p k` for `q = p^k` (the field
with `q` elements, unique up to isomorphism). Each count is the number of elements (`Nat.card`)
of the Mathlib type of the objects counted: the general and special linear groups
(`Matrix.GeneralLinearGroup`, `Matrix.SpecialLinearGroup`), the square matrices, the subspaces of
`Fin n → F` of a dimension (`Submodule`, `Module.finrank`), the points of the projective space
(`Projectivization`) and the generators of the multiplicative group. Each takes the integer part
of its arguments (Leanify asks that they be nonnegative integers and `q` a prime power). -/

namespace Leanify.FiniteFields

noncomputable section

/-- A count over the field with `q` elements: its value for Mathlib's `GaloisField p k`, where
`q = p^k`, `k ≥ 1`, for the least prime factor `p` of `q` (`0` if `q` is no prime power). -/
def overField (q : ℕ) (count : (F : Type) → [Field F] → ℕ) : ℝ :=
  if h : q.minFac.Prime ∧ 0 < q.factorization q.minFac ∧ q = q.minFac ^ q.factorization q.minFac then
    haveI : Fact q.minFac.Prime := ⟨h.1⟩
    (count (GaloisField q.minFac (q.factorization q.minFac)) : ℝ)
  else 0

/-- The order of the general linear group of degree `n` over the field with `q` elements. -/
def glOrder (n q : ℝ) : ℝ := overField ⌊q⌋₊ fun F _ => Nat.card (Matrix.GeneralLinearGroup (Fin ⌊n⌋₊) F)

/-- The order of the special linear group of degree `n` over the field with `q` elements. -/
def slOrder (n q : ℝ) : ℝ := overField ⌊q⌋₊ fun F _ => Nat.card (Matrix.SpecialLinearGroup (Fin ⌊n⌋₊) F)

/-- The number of square matrices of order `n` over the field with `q` elements. -/
def squareMatrices (n q : ℝ) : ℝ := overField ⌊q⌋₊ fun F _ => Nat.card (Matrix (Fin ⌊n⌋₊) (Fin ⌊n⌋₊) F)

/-- The number of `k`-dimensional subspaces of a space of dimension `n` (`Fin n → F`) over the
field with `q` elements. -/
def subspaces (k n q : ℝ) : ℝ :=
  overField ⌊q⌋₊ fun F _ => Nat.card {W : Submodule F (Fin ⌊n⌋₊ → F) // Module.finrank F W = ⌊k⌋₊}

/-- The number of points of the projective space of dimension `n` over the field with `q`
elements: the lines of `Fin (n + 1) → F`. -/
def projectivePoints (n q : ℝ) : ℝ := overField ⌊q⌋₊ fun F _ => Nat.card (Projectivization F (Fin (⌊n⌋₊ + 1) → F))

/-- The number of primitive elements of the field with `q` elements: the generators of its
multiplicative group. -/
def primitiveElements (q : ℝ) : ℝ := overField ⌊q⌋₊ fun F _ => Nat.card {g : Fˣ // Subgroup.zpowers g = ⊤}

end

end Leanify.FiniteFields
