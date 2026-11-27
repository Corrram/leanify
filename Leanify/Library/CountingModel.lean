import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Multinomial
import Leanify.Denote

/-! # The meaning of the counting vocabulary

Each count is the number of elements of a finite type of Mathlib (`Fintype.card`): the
subsets, arrangements, maps, compositions and lattice paths themselves, over `Fin n` for a set
of `n` elements. Each takes the integer part of its arguments (Leanify asks that they be
nonnegative integers). -/

namespace Leanify.Counting

noncomputable section
open Classical

/-- The `k`-element subsets of a set of `n` elements (Mathlib `Finset.powersetCard`). -/
def kSubsets (k n : ℝ) : ℝ := (Fintype.card {s : Finset (Fin ⌊n⌋₊) // s.card = ⌊k⌋₊} : ℝ)

/-- The subsets of a set of `n` elements (Mathlib `Finset.powerset`). -/
def subsets (n : ℝ) : ℝ := (Fintype.card (Finset (Fin ⌊n⌋₊)) : ℝ)

/-- The `k`-permutations of `n` elements: the arrangements of `k` distinct elements in order, the
injective maps from `k` positions (Mathlib `Function.Embedding`). -/
def kPermutations (k n : ℝ) : ℝ := (Fintype.card (Fin ⌊k⌋₊ ↪ Fin ⌊n⌋₊) : ℝ)

/-- The permutations of `n` elements (Mathlib `Equiv.Perm`). -/
def permutations (n : ℝ) : ℝ := (Fintype.card (Equiv.Perm (Fin ⌊n⌋₊)) : ℝ)

/-- The `k`-element multisets of `n` elements (Mathlib `Sym`). -/
def kMultisets (k n : ℝ) : ℝ := (Fintype.card (Sym (Fin ⌊n⌋₊) ⌊k⌋₊) : ℝ)

/-- The maps from a set of `k` elements to a set of `n` elements. -/
def maps (k n : ℝ) : ℝ := (Fintype.card (Fin ⌊k⌋₊ → Fin ⌊n⌋₊) : ℝ)

/-- The injective maps from a set of `k` elements to a set of `n` elements. -/
def injectiveMaps (k n : ℝ) : ℝ := (Fintype.card {f : Fin ⌊k⌋₊ → Fin ⌊n⌋₊ // Function.Injective f} : ℝ)

/-- The surjective maps from a set of `k` elements to a set of `n` elements. -/
def surjectiveMaps (k n : ℝ) : ℝ := (Fintype.card {f : Fin ⌊k⌋₊ → Fin ⌊n⌋₊ // Function.Surjective f} : ℝ)

/-- The compositions of `n` into `k` positive parts: the sequences of `k` positive integers
with sum `n`. -/
def compositionsPos (n k : ℝ) : ℝ :=
  (Fintype.card {c : Fin ⌊k⌋₊ → Fin (⌊n⌋₊ + 1) // (∀ i, 0 < (c i : ℕ)) ∧ ∑ i, (c i : ℕ) = ⌊n⌋₊} : ℝ)

/-- The compositions of `n` into `k` nonnegative parts: the sequences of `k` natural numbers
with sum `n`. -/
def compositionsNonneg (n k : ℝ) : ℝ :=
  (Fintype.card {c : Fin ⌊k⌋₊ → Fin (⌊n⌋₊ + 1) // ∑ i, (c i : ℕ) = ⌊n⌋₊} : ℝ)

/-- The lattice paths from `(0,0)` to `(m,n)` with unit steps right and up: the sequences of
`m + n` steps of which `m` go right. -/
def latticePaths (m n : ℝ) : ℝ :=
  (Fintype.card {s : Fin (⌊m⌋₊ + ⌊n⌋₊) → Bool // (Finset.univ.filter fun i => s i = true).card = ⌊m⌋₊} : ℝ)

/-- The multinomial coefficient of `a + b + c` over `a`, `b` and `c` (Mathlib `Nat.multinomial`):
the arrangements of `a + b + c` objects of three kinds, `a`, `b` and `c` of each. -/
def multinomial (a b c : ℝ) : ℝ := (Nat.multinomial Finset.univ ![⌊a⌋₊, ⌊b⌋₊, ⌊c⌋₊] : ℝ)

end

end Leanify.Counting
