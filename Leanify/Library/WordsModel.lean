import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Leanify.Denote

/-! # The meaning of the field `words`

The counts of words over an alphabet of `k` letters (`Fin k`), each the number of elements
(`Nat.card`) of the type of the words counted: the words of length `n` (`Fin n → Fin k`) with a
property, and the necklaces and de Bruijn sequences, which are cyclic words, counted up to
rotation (the classes of the cyclic words `ZMod n → Fin k` under their rotations). Each takes the
integer part of its arguments (Leanify asks that they be nonnegative integers). -/

namespace Leanify.Words

noncomputable section

/-- The number of words of length `n` over `k` letters. -/
def words (n k : ℝ) : ℝ := (Nat.card (Fin ⌊n⌋₊ → Fin ⌊k⌋₊) : ℝ)

/-- The number of palindromes of length `n` over `k` letters: the words that read the same
backwards. -/
def palindromes (n k : ℝ) : ℝ := (Nat.card {w : Fin ⌊n⌋₊ → Fin ⌊k⌋₊ // ∀ i, w i = w i.rev} : ℝ)

/-- The number of words of length `n` over `k` letters with no two equal adjacent letters. -/
def noEqualAdjacent (n k : ℝ) : ℝ :=
  (Nat.card {w : Fin ⌊n⌋₊ → Fin ⌊k⌋₊ // ∀ (i : ℕ) (h : i + 1 < ⌊n⌋₊), w ⟨i, by omega⟩ ≠ w ⟨i + 1, h⟩} : ℝ)

/-- The number of binary words of length `n` without two consecutive ones. -/
def noConsecutiveOnes (n : ℝ) : ℝ :=
  (Nat.card {w : Fin ⌊n⌋₊ → Bool // ∀ (i : ℕ) (h : i + 1 < ⌊n⌋₊), ¬(w ⟨i, by omega⟩ = true ∧ w ⟨i + 1, h⟩ = true)} : ℝ)

/-- A cyclic word is a rotation of another. -/
def IsRotation {m : ℕ} {α : Type} (x y : ZMod m → α) : Prop := ∃ r : ZMod m, ∀ i, y i = x (i + r)

/-- The number of necklaces of length `n` over `k` colours: the cyclic words of length `n` up to
rotation. -/
def necklaces (n k : ℝ) : ℝ := (Nat.card (Quot (@IsRotation ⌊n⌋₊ (Fin ⌊k⌋₊))) : ℝ)

/-- A cyclic word of length `k^n` over `k` letters is a de Bruijn sequence of order `n`: every word
of length `n` is the word of `n` consecutive letters at exactly one place. -/
def IsDeBruijn (n k : ℕ) (s : ZMod (k ^ n) → Fin k) : Prop :=
  Function.Bijective fun (i : ZMod (k ^ n)) (j : Fin n) => s (i + (j : ℕ))

/-- The number of de Bruijn sequences of order `n` over `k` letters, as cyclic sequences (up to
rotation). -/
def deBruijn (n k : ℝ) : ℝ :=
  (Nat.card (Quot fun (s t : {s // IsDeBruijn ⌊n⌋₊ ⌊k⌋₊ s}) => IsRotation s.1 t.1) : ℝ)

end

end Leanify.Words
