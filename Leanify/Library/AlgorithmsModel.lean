import Mathlib.Data.Tree.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Leanify.Denote

/-! # The meaning of the field `algorithms`

The classical algorithms as programs that count their comparisons, run on the inputs of `n`
distinct keys (the orders of `0, …, n-1`, `List.ofFn` of a permutation): binary search (three-way
comparisons with the middle key, for every key present), insertion sort (inserting each key into
the sorted prefix from its largest end), top-down merge sort (halves of sizes `⌈n/2⌉` and
`⌊n/2⌋`), quicksort (the first key as the pivot, compared with every other), the scan for the
maximum and the scan in pairs for the maximum and the minimum. The worst case is the maximum over
the inputs and the expectation the mean over them. The Tower of Hanoi needs as many moves as the
distance of its first and last positions in the graph of the legal moves (Mathlib
`SimpleGraph.dist`); the trees are Mathlib's `BinaryTree`s, their height counted in edges. The
formulas are theorems, not definitions. -/

namespace Leanify.Algorithms

noncomputable section

/-- The keys `0, …, n-1` in the order of a permutation. -/
def input {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

/-- The worst case of a count over the inputs of `n` distinct keys. -/
def worst (n : ℕ) (c : List ℕ → ℕ) : ℕ := Finset.univ.sup fun σ : Equiv.Perm (Fin n) => c (input σ)

/-- The comparisons of binary search for the key `x` among the sorted keys `lo, …, hi-1`
(`fuel` bounds the steps). -/
def binarySearch : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | f + 1, x, lo, hi =>
    if hi ≤ lo then 0 else
    let mid := (lo + hi) / 2
    if x = mid then 1 else if x < mid then 1 + binarySearch f x lo mid else 1 + binarySearch f x (mid + 1) hi

/-- The worst-case number of comparisons of binary search on `n` sorted keys, over the keys
present. -/
def binarySearchWorst (n : ℝ) : ℝ :=
  ((Finset.range ⌊n⌋₊).sup fun x => binarySearch (⌊n⌋₊ + 1) x 0 ⌊n⌋₊ : ℕ)

/-- The comparisons of inserting `x` into a sorted list given from its largest key down. -/
def insertDesc (x : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([x], 0)
  | y :: ys => if y < x then (x :: y :: ys, 1) else let r := insertDesc x ys; (y :: r.1, r.2 + 1)

/-- Insertion sort, the sorted prefix kept from its largest key down, and its comparisons. -/
def insertionSort : List ℕ → List ℕ → ℕ → ℕ
  | [], _, c => c
  | x :: xs, sorted, c => let r := insertDesc x sorted; insertionSort xs r.1 (c + r.2)

def insertionWorst (n : ℝ) : ℝ := (worst ⌊n⌋₊ fun l => insertionSort l [] 0 : ℕ)

/-- Merging two sorted lists, and its comparisons. -/
def merge : List ℕ → List ℕ → List ℕ × ℕ
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
    if x ≤ y then let r := merge xs (y :: ys); (x :: r.1, r.2 + 1)
    else let r := merge (x :: xs) ys; (y :: r.1, r.2 + 1)
termination_by xs ys => xs.length + ys.length

/-- Top-down merge sort (`fuel` bounds the depth), and its comparisons. -/
def mergeSort : ℕ → List ℕ → List ℕ × ℕ
  | 0, l => (l, 0)
  | f + 1, l =>
    if l.length ≤ 1 then (l, 0) else
    let a := mergeSort f (l.take ((l.length + 1) / 2))
    let b := mergeSort f (l.drop ((l.length + 1) / 2))
    let m := merge a.1 b.1
    (m.1, a.2 + b.2 + m.2)

def mergeWorst (n : ℝ) : ℝ := (worst ⌊n⌋₊ fun l => (mergeSort l.length l).2 : ℕ)

/-- Quicksort with the first key as the pivot (`fuel` bounds the depth), and its comparisons. -/
def quickSort : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | f + 1, p :: xs => xs.length + quickSort f (xs.filter (· < p)) + quickSort f (xs.filter (p < ·))

/-- The expected number of comparisons of quicksort on a uniformly random order of `n` keys. -/
def quickExpected (n : ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin ⌊n⌋₊), (quickSort ⌊n⌋₊ (input σ) : ℝ)) / (Fintype.card (Equiv.Perm (Fin ⌊n⌋₊)) : ℝ)

/-- The scan for the maximum from the first key (each later key compared with the maximum so
far), and its comparisons. -/
def maxScan : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | x :: xs => xs.foldl (fun (m, c) y => (max m y, c + 1)) (x, 0)

/-- The scan in pairs for the maximum and the minimum, from the maximum and the minimum so far:
each pair is compared, its larger key with the maximum and its smaller with the minimum. Returns
the maximum, the minimum and the comparisons. -/
def pairScan : ℕ × ℕ × ℕ → List ℕ → ℕ × ℕ × ℕ
  | (mx, mn, c), a :: b :: rest =>
    let hi := max a b
    let lo := min a b
    pairScan (max mx hi, min mn lo, c + 3) rest
  | st, _ => st

/-- The maximum and the minimum by pairs: the first key starts both (for an odd number of keys),
or the first pair, compared, does (for an even number). -/
def maxMinPairs : List ℕ → ℕ × ℕ × ℕ
  | [] => (0, 0, 0)
  | [x] => (x, x, 0)
  | l@(a :: b :: rest) =>
    if l.length % 2 = 0 then pairScan (max a b, min a b, 1) rest else pairScan (a, a, 0) (b :: rest)

def maxWorst (n : ℝ) : ℝ := (worst ⌊n⌋₊ fun l => (maxScan l).2 : ℕ)
def maxMinWorst (n : ℝ) : ℝ := (worst ⌊n⌋₊ fun l => (maxMinPairs l).2.2 : ℕ)

/-- The positions of the Tower of Hanoi with `n` disks (the peg of each disk, disk `0` the
smallest), adjacent when one legal move leads from one to the other: a disk with no smaller disk
on its peg or on the peg it moves to. -/
def hanoi (n : ℕ) : SimpleGraph (Fin n → Fin 3) where
  Adj s t := ∃ d, s d ≠ t d ∧ (∀ e, e ≠ d → s e = t e) ∧ ∀ e, e < d → s e ≠ s d ∧ s e ≠ t d
  symm := ⟨fun s t ⟨d, h1, h2, h3⟩ => ⟨d, h1.symm, fun e he => (h2 e he).symm, fun e he => by
    have := h3 e he
    rw [h2 e (ne_of_lt he)] at this
    exact ⟨this.2, this.1⟩⟩⟩
  loopless := ⟨fun s ⟨d, h, _⟩ => h rfl⟩

/-- The number of moves of the Tower of Hanoi with `n` disks: from all on the first peg to all on
the last. -/
def hanoiMoves (n : ℝ) : ℝ := ((hanoi ⌊n⌋₊).dist (fun _ => 0) (fun _ => 2) : ℕ)

/-- The perfect binary tree of height `h` (in edges). -/
def perfect : ℕ → BinaryTree Unit
  | 0 => .node () .nil .nil
  | h + 1 => .node () (perfect h) (perfect h)

def perfectNodes (h : ℝ) : ℝ := ((perfect ⌊h⌋₊).numNodes : ℝ)

/-- The minimal height (in edges) of a binary tree with `n` nodes. -/
def minHeight (n : ℝ) : ℝ := by
  classical exact
  if h : ∃ k : ℕ, ∃ t : BinaryTree Unit, t.numNodes = ⌊n⌋₊ ∧ t.height = k + 1 then ((Nat.find h : ℕ) : ℝ) else 0

end

end Leanify.Algorithms
