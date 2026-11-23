import Leanify.Denote
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! # The meaning of the field `arithmetic`

The arithmetic functions of Mathlib as functions of real numbers: each takes the integer
part of its arguments (Leanify asks that they be positive integers, or primes, where the
function is meant). -/

namespace Leanify.Arithmetic

/-- Euler's totient function. -/
noncomputable def totient (n : ℝ) : ℝ := (Nat.totient ⌊n⌋₊ : ℝ)

/-- The Möbius function. -/
noncomputable def moebius (n : ℝ) : ℝ := (ArithmeticFunction.moebius ⌊n⌋₊ : ℝ)

/-- The number of positive divisors. -/
noncomputable def numDivisors (n : ℝ) : ℝ := ((Nat.divisors ⌊n⌋₊).card : ℝ)

/-- `σ_k(n)`, the sum of the `k`-th powers of the divisors of `n`. -/
noncomputable def sigma (k n : ℝ) : ℝ := (ArithmeticFunction.sigma ⌊k⌋₊ ⌊n⌋₊ : ℝ)

/-- `π(x)`, the number of primes `p ≤ x`. -/
noncomputable def primeCounting (x : ℝ) : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- The `n`-th prime, `p_1 = 2`. -/
noncomputable def nthPrime (n : ℝ) : ℝ := (Nat.nth Nat.Prime (⌊n⌋₊ - 1) : ℝ)

/-- `ω(n)`, the number of distinct prime factors. -/
noncomputable def omega (n : ℝ) : ℝ := (ArithmeticFunction.cardDistinctFactors ⌊n⌋₊ : ℝ)

/-- `Ω(n)`, the number of prime factors counted with multiplicity. -/
noncomputable def bigOmega (n : ℝ) : ℝ := (ArithmeticFunction.cardFactors ⌊n⌋₊ : ℝ)

/-- The exponent of the prime `p` in `n`. -/
noncomputable def padicVal (p n : ℝ) : ℝ := (padicValNat ⌊p⌋₊ ⌊n⌋₊ : ℝ)

/-- The multiplicative order of the integer `a` modulo `n`. -/
noncomputable def orderMod (a n : ℝ) : ℝ := (orderOf (((⌊a⌋ : ℤ) : ZMod ⌊n⌋₊)) : ℝ)

/-- The sum of the digits of `n` in base `b`. -/
noncomputable def digitSum (b n : ℝ) : ℝ := ((Nat.digits ⌊b⌋₊ ⌊n⌋₊).sum : ℝ)

end Leanify.Arithmetic
