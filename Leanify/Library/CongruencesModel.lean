import Leanify.Denote
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement

/-! # The meaning of the field `congruences`

Residues of integers modulo `n`, in Mathlib's `ZMod n`; each function takes the integer
part of its arguments. -/

namespace Leanify.Congruences

noncomputable section
open Classical

/-- The residue of `⌊a⌋` modulo `⌊n⌋`. -/
def res (a n : ℝ) : ZMod ⌊n⌋₊ := ((⌊a⌋ : ℤ) : ZMod ⌊n⌋₊)

def QuadraticResidue (a n : ℝ) : Prop := IsSquare (res a n)

/-- The Legendre symbol: `0` if `p ∣ a`, `1` if `a` is a square modulo `p`, `-1` otherwise. -/
def legendre (a p : ℝ) : ℝ := if res a p = 0 then 0 else if IsSquare (res a p) then 1 else -1

/-- The order of `a` modulo `n` is `φ(n)`. -/
def PrimitiveRoot (a n : ℝ) : Prop := orderOf (res a n) = Nat.totient ⌊n⌋₊

def HasPrimitiveRoot (n : ℝ) : Prop := ∃ g : ℕ, IsUnit ((g : ℤ) : ZMod ⌊n⌋₊) ∧ orderOf ((g : ℤ) : ZMod ⌊n⌋₊) = Nat.totient ⌊n⌋₊

def inverse (a n : ℝ) : ℝ := ((res a n)⁻¹).val

def leastPrimitiveRoot (n : ℝ) : ℝ :=
  ((sInf {g : ℕ | IsUnit ((g : ℤ) : ZMod ⌊n⌋₊) ∧ orderOf ((g : ℤ) : ZMod ⌊n⌋₊) = Nat.totient ⌊n⌋₊} : ℕ) : ℝ)

def numResidues (n : ℝ) : ℝ := Nat.card {x : ZMod ⌊n⌋₊ // IsUnit x ∧ IsSquare x}
def numPrimitiveRoots (n : ℝ) : ℝ := Nat.card {x : ZMod ⌊n⌋₊ // IsUnit x ∧ orderOf x = Nat.totient ⌊n⌋₊}

end

end Leanify.Congruences
