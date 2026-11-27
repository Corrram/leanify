import Leanify.Library.Core

/-! # Vocabulary: analysis of algorithms

The operation counts of the classical algorithms, by the size of the input (`We write $B(n)$
for the number of comparisons of binary search on $n$ elements.`).

* notions: the worst-case number of comparisons of binary search, insertion sort and merge
  sort on `n` elements; the expected number of comparisons of quicksort; the
  information-theoretic lower bound `⌈log₂ n!⌉` for sorting by comparisons; the comparisons to
  find the maximum and both the maximum and the minimum; the number of moves of the Tower of
  Hanoi; the critical exponent `log a / log b` of the recurrence `T(n) = a T(n/b) + f(n)` (master
  theorem); the number of nodes of a perfect binary tree of height `h` and the minimal height of
  a binary tree with `n` nodes.

The counts are constants, interpreted by the declarations of `Leanify/Library/AlgorithmsModel.lean`:
the algorithms as programs that count their comparisons, run on the inputs of `n` distinct keys
(worst case: the maximum over them; expectation: the mean), the least number of moves of the
Tower of Hanoi as a distance in the graph of its legal moves (Mathlib `SimpleGraph.dist`), and
Mathlib's `BinaryTree`s. Their formulas (`⌊log₂ n⌋ + 1`, `n(n-1)/2`, `n⌈log₂ n⌉ - 2^{⌈log₂ n⌉} + 1`,
`2(n+1)H_n - 4n`, `n - 1`, `⌈3n/2⌉ - 2`, `2^n - 1`, `2^{h+1} - 1`, `⌊log₂ n⌋`) are theorems, not
definitions; the lower bound and the critical exponent are the formulas they name. -/

namespace Leanify.Algorithms
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def log (x : B) : B := app (prim (.realFn .log)) x
def ceil (x : B) : B := app (prim .ceil) x
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def binarySearch : Nat := 0
def insertion : Nat := 1
def merge : Nat := 2
def quick : Nat := 3
def maxScan : Nat := 4
def maxMin : Nat := 5
def hanoi : Nat := 6
def perfectNodes : Nat := 7
def minHeight : Nat := 8
end Const

def size (name : Phrase) (dom : B → B) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real dom], doc, value := .const c }
def sizeF (name : Phrase) (dom : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real dom], doc, value := close <| lamT .real dom body }

def vocab : Vocab where
  consts := List.replicate 9 (.real ⟶ .real)
  constNames := [w!"B_{#}", w!"I_{#}", w!"M_{#}", w!"\\mathbb{E}Q_{#}", w!"\\max_{#}", w!"\\operatorname{maxmin}_{#}", w!"H_{#}",
    w!"\\#T_{#}", w!"h_{#}"]
  constLean := [w!"Leanify.Algorithms.binarySearchWorst", w!"Leanify.Algorithms.insertionWorst", w!"Leanify.Algorithms.mergeWorst",
    w!"Leanify.Algorithms.quickExpected", w!"Leanify.Algorithms.maxWorst", w!"Leanify.Algorithms.maxMinWorst",
    w!"Leanify.Algorithms.hanoiMoves", w!"Leanify.Algorithms.perfectNodes", w!"Leanify.Algorithms.minHeight"]
  modules := [w!"Leanify.Library.AlgorithmsModel"]
  notions := [
    size phrase!"number of comparisons of binary search on $v$ elements" posInt Const.binarySearch
      "in the worst case, three-way comparisons with the middle key (`⌊log₂ n⌋ + 1`)",
    size phrase!"number of comparisons of insertion sort on $v$ elements" posInt Const.insertion
      "in the worst case (`n(n-1)/2`)",
    size phrase!"number of comparisons of merge sort on $v$ elements" posInt Const.merge
      "in the worst case, top-down (`n⌈log₂ n⌉ - 2^{⌈log₂ n⌉} + 1`)",
    size phrase!"expected number of comparisons of quicksort on $v$ elements" posInt Const.quick
      "for a uniformly random order of distinct keys, the first key the pivot (`2(n+1)H_n - 4n`)",
    sizeF phrase!"lower bound for sorting $v$ elements" posInt (fun n => ceil (div (log (fact n)) (log (num 2))))
      "`⌈log₂ n!⌉`: comparisons needed in the worst case by any comparison sort",
    size phrase!"number of comparisons to find the maximum of $v$ elements" posInt Const.maxScan
      "by a scan, in the worst case (`n - 1`)",
    size phrase!"number of comparisons to find the maximum and the minimum of $v$ elements" posInt Const.maxMin
      "by a scan in pairs, in the worst case (`⌈3n/2⌉ - 2`)",
    size phrase!"number of moves of the Tower of Hanoi with $v$ disks" natP Const.hanoi
      "the least number of legal moves from one peg to another (`2^n - 1`)",
    { name := phrase!"critical exponent for $v$ subproblems with shrinking factor $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun a => le (num 1) a, dom2 .real fun _ b => lt (num 1) b],
      doc := "`log a / log b` = `log_b a`, for `T(n) = a T(n/b) + f(n)` (master theorem)",
      value := close <| lamT .real (fun a => le (num 1) a) fun a => lamT .real (fun b => lt (num 1) b) fun b => div (log a) (log b) },
    size phrase!"number of nodes of a perfect binary tree of height $v$" natP Const.perfectNodes
      "Mathlib `BinaryTree.numNodes` of the perfect tree (`2^{h+1} - 1`)",
    size phrase!"minimal height of a binary tree with $v$ nodes" posInt Const.minHeight
      "the least height in edges of a Mathlib `BinaryTree` with `n` nodes (`⌊log₂ n⌋`)"]

end Leanify.Algorithms
