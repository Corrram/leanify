import Leanify.Denote
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Integers among the real numbers

Leanify's numbers are real numbers, and `x ∈ ℤ` is `Prelude.isInt x`. What every reader
uses about integers without saying so is proved here once: sums, differences and
products of integers are integers, and between two integers there is a gap of one.
The standard tactic `leanify_step` uses these facts (`leanify_int`). -/

namespace Leanify.Prelude

theorem isInt_zero : isInt (0 : ℝ) := ⟨0, by simp⟩
theorem isInt_one : isInt (1 : ℝ) := ⟨1, by simp⟩
theorem isInt_ofNat (n : ℕ) [n.AtLeastTwo] : isInt (OfNat.ofNat n : ℝ) :=
  ⟨(OfNat.ofNat n : ℤ), by norm_num⟩

theorem isInt.add {x y : ℝ} (hx : isInt x) (hy : isInt y) : isInt (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; ring⟩
theorem isInt.sub {x y : ℝ} (hx : isInt x) (hy : isInt y) : isInt (x - y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a - b, by push_cast; ring⟩
theorem isInt.mul {x y : ℝ} (hx : isInt x) (hy : isInt y) : isInt (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by push_cast; ring⟩
theorem isInt.neg {x : ℝ} (hx : isInt x) : isInt (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by push_cast; ring⟩
theorem isInt.pow {x : ℝ} (hx : isInt x) (n : ℕ) : isInt (x ^ n) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨a ^ n, by push_cast; ring⟩
theorem isNat.isInt {x : ℝ} (hx : isNat x) : isInt x := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨(a : ℤ), by simp⟩
theorem isNat.nonneg {x : ℝ} (hx : isNat x) : 0 ≤ x := by
  obtain ⟨a, rfl⟩ := hx; positivity

/-- Between two integers there is a gap of one. -/
theorem isInt.add_one_le_of_lt {x y : ℝ} (hx : isInt x) (hy : isInt y) (h : x < y) : x + 1 ≤ y := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast h)

end Leanify.Prelude

namespace Leanify

/-- `leanify_int` proves that a real number is an integer: a hypothesis, a numeral, or a
sum, difference, product, negative or power of integers. -/
syntax "leanify_int" : tactic

macro_rules | `(tactic| leanify_int) => `(tactic| first
  | assumption
  | exact Leanify.Prelude.isInt_zero
  | exact Leanify.Prelude.isInt_one
  | exact Leanify.Prelude.isInt_ofNat _
  | (apply Leanify.Prelude.isInt.add <;> leanify_int)
  | (apply Leanify.Prelude.isInt.sub <;> leanify_int)
  | (apply Leanify.Prelude.isInt.mul <;> leanify_int)
  | (apply Leanify.Prelude.isInt.neg; leanify_int)
  | (apply Leanify.Prelude.isInt.pow; leanify_int)
  | (apply Leanify.Prelude.isNat.isInt; assumption))

end Leanify
