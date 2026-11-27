import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Leanify.Denote

/-! # The meaning of the field `orthogonalpolynomials`

The polynomials of Mathlib, as functions of a real number: the Chebyshev polynomials
`Polynomial.Chebyshev.T` and `U` (by their recurrences), the probabilists' Hermite polynomials
`Polynomial.hermite`, and the Legendre polynomials from Mathlib's shifted Legendre polynomials
`Polynomial.shiftedLegendre n` (`∑_k (-1)^k \binom{n}{k}\binom{n+k}{n} x^k`) at `(1 - x)/2`. Their
explicit sums are theorems, not definitions. -/

namespace Leanify.OrthogonalPolynomials

noncomputable section

/-- The Legendre polynomial of degree `n`. -/
def legendre (n : ℝ) (x : ℝ) : ℝ := ((Polynomial.shiftedLegendre ⌊n⌋₊).map (Int.castRingHom ℝ)).eval ((1 - x) / 2)

/-- The probabilists' Hermite polynomial of degree `n`. -/
def hermiteProb (n : ℝ) (x : ℝ) : ℝ := ((Polynomial.hermite ⌊n⌋₊).map (Int.castRingHom ℝ)).eval x

/-- The Chebyshev polynomial of the first kind of degree `n`. -/
def chebT (n : ℝ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ (⌊n⌋₊ : ℤ)).eval x

/-- The Chebyshev polynomial of the second kind of degree `n`. -/
def chebU (n : ℝ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.U ℝ (⌊n⌋₊ : ℤ)).eval x

end

end Leanify.OrthogonalPolynomials
