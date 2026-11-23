import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Leanify.Denote

/-! # The meaning of the combinatorics vocabulary

The counting numbers of Mathlib as functions of real numbers: each takes the integer part
of its arguments (Leanify asks that they be nonnegative integers). -/

namespace Leanify.Combinatorics

/-- The `n`-th Fibonacci number. -/
noncomputable def fib (n : ℝ) : ℝ := (Nat.fib ⌊n⌋₊ : ℝ)

/-- The `n`-th Catalan number. -/
noncomputable def catalan (n : ℝ) : ℝ := (_root_.catalan ⌊n⌋₊ : ℝ)

/-- The `n`-th Bell number. -/
noncomputable def bell (n : ℝ) : ℝ := (Nat.bell ⌊n⌋₊ : ℝ)

/-- The number of derangements of `n` elements. -/
noncomputable def derangements (n : ℝ) : ℝ := (numDerangements ⌊n⌋₊ : ℝ)

/-- The number of partitions of the integer `n`. -/
noncomputable def partitions (n : ℝ) : ℝ := (Fintype.card (Nat.Partition ⌊n⌋₊) : ℝ)

/-- The Stirling number of the second kind. -/
noncomputable def stirling2 (n k : ℝ) : ℝ := (Nat.stirlingSecond ⌊n⌋₊ ⌊k⌋₊ : ℝ)

/-- The unsigned Stirling number of the first kind. -/
noncomputable def stirling1 (n k : ℝ) : ℝ := (Nat.stirlingFirst ⌊n⌋₊ ⌊k⌋₊ : ℝ)

end Leanify.Combinatorics
