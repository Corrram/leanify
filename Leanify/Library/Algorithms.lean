import Leanify.Library.Core

/-! # Vocabulary: analysis of algorithms

The operation counts of the classical algorithms, by the size of the input (`We write $B(n)$
for the number of comparisons of binary search on $n$ elements.`).

* notions: the worst-case number of comparisons of binary search (`⌊log₂ n⌋ + 1`), insertion
  sort (`n(n-1)/2`) and merge sort (`n⌈log₂ n⌉ - 2^{⌈log₂ n⌉} + 1`) on `n` elements; the expected
  number of comparisons of quicksort (`2(n+1)H_n - 4n`); the information-theoretic lower bound
  `⌈log₂ n!⌉` for sorting by comparisons; the comparisons to find the maximum (`n - 1`) and
  both the maximum and the minimum (`⌈3n/2⌉ - 2`); the number of moves `2^n - 1` of the Tower of
  Hanoi; the critical exponent `log a / log b` of the recurrence `T(n) = a T(n/b) + f(n)`
  (master theorem); the number of nodes `2^{h+1} - 1` of a perfect binary tree of height `h` and
  the minimal height `⌊log₂ n⌋` of a binary tree with `n` nodes.

Every meaning is a term of the core language. -/

namespace Leanify.Algorithms
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def log (x : B) : B := app (prim (.realFn .log)) x
def ceil (x : B) : B := app (prim .ceil) x
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
/-- `⌊log₂ n⌋ + 1`: the number of binary digits of `n ≥ 1`. -/
def bits (n : B) : B := theR fun l => and (posInt l) (and (le (zpow (num 2) (sub l (num 1))) n) (lt n (zpow (num 2) l)))
/-- `⌈log₂ n⌉` for `n ≥ 1`. -/
def clog (n : B) : B := theR fun c => and (natP c) (and (le n (zpow (num 2) c)) (or (eq c (num 0)) (lt (zpow (num 2) (sub c (num 1))) n)))
def size (name : Phrase) (dom : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real dom], doc, value := close <| lamT .real dom body }

def vocab : Vocab where
  notions := [
    size phrase!"number of comparisons of binary search on $v$ elements" posInt bits
      "`⌊log₂ n⌋ + 1`, in the worst case",
    size phrase!"number of comparisons of insertion sort on $v$ elements" posInt (fun n => div (mul n (sub n (num 1))) (num 2))
      "`n(n-1)/2`, in the worst case",
    size phrase!"number of comparisons of merge sort on $v$ elements" posInt
      (fun n => add (sub (mul n (clog n)) (zpow (num 2) (clog n))) (num 1)) "`n⌈log₂ n⌉ - 2^{⌈log₂ n⌉} + 1`, in the worst case",
    size phrase!"expected number of comparisons of quicksort on $v$ elements" posInt
      (fun n => sub (mul (mul (num 2) (add n (num 1))) (finSum (num 1) n fun k => div (num 1) k)) (mul (num 4) n))
      "`2(n+1)H_n - 4n`, for a uniformly random order of distinct keys",
    size phrase!"lower bound for sorting $v$ elements" posInt (fun n => ceil (div (log (fact n)) (log (num 2))))
      "`⌈log₂ n!⌉`: comparisons needed in the worst case by any comparison sort",
    size phrase!"number of comparisons to find the maximum of $v$ elements" posInt (fun n => sub n (num 1)) "`n - 1`",
    size phrase!"number of comparisons to find the maximum and the minimum of $v$ elements" posInt
      (fun n => sub (ceil (div (mul (num 3) n) (num 2))) (num 2)) "`⌈3n/2⌉ - 2`",
    size phrase!"number of moves of the Tower of Hanoi with $v$ disks" natP (fun n => sub (zpow (num 2) n) (num 1)) "`2^n - 1`",
    { name := phrase!"critical exponent for $v$ subproblems with shrinking factor $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun a => le (num 1) a, dom2 .real fun _ b => lt (num 1) b],
      doc := "`log a / log b` = `log_b a`, for `T(n) = a T(n/b) + f(n)` (master theorem)",
      value := close <| lamT .real (fun a => le (num 1) a) fun a => lamT .real (fun b => lt (num 1) b) fun b => div (log a) (log b) },
    size phrase!"number of nodes of a perfect binary tree of height $v$" natP (fun h => sub (zpow (num 2) (add h (num 1))) (num 1))
      "`2^{h+1} - 1`",
    size phrase!"minimal height of a binary tree with $v$ nodes" posInt (fun n => sub (bits n) (num 1)) "`⌊log₂ n⌋`"]

end Leanify.Algorithms
