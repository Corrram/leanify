import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Leanify.Denote

/-! # The meaning of the field `combinatorialgames`

The games by their moves: a position is losing (for the player to move) when every move leads
to a winning one, and a winning move leads to a losing one; Nim with three heaps moves a heap
to a smaller one. The Grundy value of a position is the least natural number that is not the
Grundy value of a position reached in one move (the minimal excludant). Bouton's criterion
(`a ⊕ b ⊕ c = 0`) and the Grundy values `n mod (k+1)` of the subtraction game are theorems, not
definitions. -/

namespace Leanify.CombinatorialGames

noncomputable section

/-- The Nim position with heaps `a`, `b`, `c` is losing for the player to move (`fuel` bounds
the length of the game, which the total of the heaps does). -/
def nimLosing : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | f + 1, a, b, c =>
    (List.range a).all (fun a' => !nimLosing f a' b c) &&
    (List.range b).all (fun b' => !nimLosing f a b' c) &&
    (List.range c).all (fun c' => !nimLosing f a b c')

/-- The Nim position is losing. -/
def NimLosing (a b c : ℕ) : Prop := nimLosing (a + b + c + 1) a b c = true

/-- The number of winning moves in the Nim position with heaps `a`, `b`, `c`: the moves to a
losing position. -/
def winningMoves (a b c : ℝ) : ℝ := by
  classical exact
  ((((Finset.range ⌊a⌋₊).filter fun a' => NimLosing a' ⌊b⌋₊ ⌊c⌋₊).card +
    ((Finset.range ⌊b⌋₊).filter fun b' => NimLosing ⌊a⌋₊ b' ⌊c⌋₊).card +
    ((Finset.range ⌊c⌋₊).filter fun c' => NimLosing ⌊a⌋₊ ⌊b⌋₊ c').card : ℕ) : ℝ)

/-- The minimal excludant of a finite set of natural numbers: the least one not in it. -/
def mex (s : Finset ℕ) : ℕ := by
  classical exact if h : ∃ m, m ∉ s then Nat.find h else 0

/-- The Grundy value of a heap of `n` in the subtraction game with moves `1, …, k`. -/
def grundy (k : ℕ) (n : ℕ) : ℕ :=
  mex ((Finset.Icc 1 (min k n)).attach.image fun j => grundy k (n - j.1))
termination_by n
decreasing_by
  have := Finset.mem_Icc.mp j.2
  omega

def grundyValue (n k : ℝ) : ℝ := (grundy ⌊k⌋₊ ⌊n⌋₊ : ℕ)

end

end Leanify.CombinatorialGames
