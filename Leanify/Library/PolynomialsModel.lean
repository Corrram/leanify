import Leanify.Denote
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic

/-! # The meaning of the field `polynomials`

A polynomial is a real function `f` with `f x = p.eval x` for a polynomial `p : ℝ[X]`, which
is then unique (`toPoly f`); the notions of the field are those of `toPoly f`. -/

namespace Leanify.Polynomials
open Polynomial

/-- `f` is given by a polynomial with real coefficients. -/
def IsPoly (f : ℝ → ℝ) : Prop := ∃ p : ℝ[X], ∀ x, f x = p.eval x

open Classical in
/-- The polynomial of a polynomial function (any one: there is only one), `0` for another function. -/
noncomputable def toPoly (f : ℝ → ℝ) : ℝ[X] := if h : IsPoly f then h.choose else 0

noncomputable def degree (f : ℝ → ℝ) : ℝ := ((toPoly f).natDegree : ℝ)
noncomputable def leadingCoeff (f : ℝ → ℝ) : ℝ := (toPoly f).leadingCoeff
noncomputable def coeff (k : ℝ) (f : ℝ → ℝ) : ℝ := (toPoly f).coeff ⌊k⌋₊

open Classical in
/-- The number of distinct real roots. -/
noncomputable def numRoots (f : ℝ → ℝ) : ℝ := ((toPoly f).roots.toFinset.card : ℝ)

def IntCoeffs (f : ℝ → ℝ) : Prop := ∀ k, ∃ z : ℤ, (toPoly f).coeff k = z
def RatCoeffs (f : ℝ → ℝ) : Prop := ∀ k, ∃ q : ℚ, (toPoly f).coeff k = q
def Monic (f : ℝ → ℝ) : Prop := (toPoly f).Monic

/-- Irreducible in `ℚ[X]`: the polynomial of a rational polynomial that is irreducible. -/
def IrreducibleQ (f : ℝ → ℝ) : Prop :=
  ∃ q : ℚ[X], q.map (algebraMap ℚ ℝ) = toPoly f ∧ Irreducible q

def IrreducibleR (f : ℝ → ℝ) : Prop := Irreducible (toPoly f)

open Classical in
noncomputable def rootMultiplicity (a : ℝ) (f : ℝ → ℝ) : ℝ := ((toPoly f).rootMultiplicity a : ℝ)

end Leanify.Polynomials
