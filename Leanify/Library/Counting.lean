import Leanify.Library.Core

/-! # Vocabulary: counting

The standard counts of enumerative combinatorics (`the number of $k$-element subsets of a set
of $n$ elements`), each the number of elements of a finite type of Mathlib: the subsets,
arrangements, maps, compositions and lattice paths themselves, over `Fin n` for a set of `n`
elements.

* subsets and arrangements: the number of `k`-element subsets of a set of `n` elements
  (`{s : Finset (Fin n) // s.card = k}`), of subsets of a set of `n` elements
  (`Finset (Fin n)`), of `k`-permutations of `n` elements (`Fin k ↪ Fin n`), of permutations
  of `n` elements (`Equiv.Perm (Fin n)`), of `k`-element multisets of `n` elements
  (`Sym (Fin n) k`);
* maps: the number of maps from a set of `k` elements to a set of `n` elements
  (`Fin k → Fin n`), of injective maps, of surjective maps (`Function.Injective`,
  `Function.Surjective`);
* compositions and paths: the number of compositions of `n` into `k` positive parts, into `k`
  nonnegative parts (the sequences of `k` such numbers with sum `n`), and of lattice paths from
  `(0,0)` to `(m,n)` with unit steps right and up (the sequences of `m + n` steps of which `m`
  go right);
* the multinomial coefficient of `n` over `a` and `b` and `c` (Mathlib `Nat.multinomial`,
  `a + b + c = n`).

The counts are constants, interpreted by the declarations of
`Leanify/Library/CountingModel.lean`; their arguments are nonnegative integers. -/

namespace Leanify.Counting
open Build Core

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def kSubsets : Nat := 0
def subsets : Nat := 1
def kPermutations : Nat := 2
def permutations : Nat := 3
def kMultisets : Nat := 4
def maps : Nat := 5
def injectiveMaps : Nat := 6
def surjectiveMaps : Nat := 7
def compositionsPos : Nat := 8
def compositionsNonneg : Nat := 9
def latticePaths : Nat := 10
def multinomial : Nat := 11
end Const

def natP (n : B) : B := and (isInt n) (le (num 0) n)

/-- A count of two nonnegative integers (the arguments in the order of the phrase). -/
def count2 (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real natP, dom2 .real fun _ b => natP b], doc,
    value := .const c }

/-- A count of one nonnegative integer. -/
def count1 (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real natP], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real]
  constNames := [w!"\\operatorname{Sub}(#1,#2)", w!"\\operatorname{Sub}", w!"\\operatorname{Perm}(#1,#2)",
    w!"\\operatorname{Perm}", w!"\\operatorname{Mult}(#1,#2)", w!"\\operatorname{Map}(#1,#2)",
    w!"\\operatorname{Inj}(#1,#2)", w!"\\operatorname{Surj}(#1,#2)", w!"\\operatorname{Comp}^{+}(#1,#2)",
    w!"\\operatorname{Comp}(#1,#2)", w!"\\operatorname{Path}(#1,#2)", w!"\\binom{#1+#2+#3}{#1,#2,#3}"]
  constLean := [w!"Leanify.Counting.kSubsets", w!"Leanify.Counting.subsets", w!"Leanify.Counting.kPermutations",
    w!"Leanify.Counting.permutations", w!"Leanify.Counting.kMultisets", w!"Leanify.Counting.maps",
    w!"Leanify.Counting.injectiveMaps", w!"Leanify.Counting.surjectiveMaps", w!"Leanify.Counting.compositionsPos",
    w!"Leanify.Counting.compositionsNonneg", w!"Leanify.Counting.latticePaths", w!"Leanify.Counting.multinomial"]
  modules := [w!"Leanify.Library.CountingModel"]
  notions := [
    count2 phrase!"number of $v$-element subsets of a set of $v$ elements" Const.kSubsets
      "the `k`-element subsets of `Fin n` (Mathlib `Finset`; `\\\\binom{n}{k}`)",
    count1 phrase!"number of subsets of a set of $v$ elements" Const.subsets
      "the subsets of `Fin n` (Mathlib `Finset`; `2^n`)",
    count2 phrase!"number of $v$-permutations of $v$ elements" Const.kPermutations
      "the arrangements of `k` distinct elements of `Fin n` in order (Mathlib `Fin k ↪ Fin n`; `n!/(n-k)!` for `k ≤ n`)",
    count1 phrase!"number of permutations of $v$ elements" Const.permutations
      "the permutations of `Fin n` (Mathlib `Equiv.Perm`; `n!`)",
    count2 phrase!"number of $v$-element multisets of $v$ elements" Const.kMultisets
      "the `k`-element multisets of `Fin n` (Mathlib `Sym`; `\\\\binom{n+k-1}{k}`)",
    count2 phrase!"number of maps from a set of $v$ elements to a set of $v$ elements" Const.maps
      "the maps `Fin k → Fin n` (`n^k`)",
    count2 phrase!"number of injective maps from a set of $v$ elements to a set of $v$ elements" Const.injectiveMaps
      "the injective maps `Fin k → Fin n` (Mathlib `Function.Injective`)",
    count2 phrase!"number of surjective maps from a set of $v$ elements to a set of $v$ elements" Const.surjectiveMaps
      "the surjective maps `Fin k → Fin n` (Mathlib `Function.Surjective`)",
    count2 phrase!"number of compositions of $v$ into $v$ positive parts" Const.compositionsPos
      "the sequences of `k` positive integers with sum `n` (`\\\\binom{n-1}{k-1}` for `1 ≤ k ≤ n`)",
    count2 phrase!"number of compositions of $v$ into $v$ nonnegative parts" Const.compositionsNonneg
      "the sequences of `k` nonnegative integers with sum `n` (`\\\\binom{n+k-1}{k-1}` for `k ≥ 1`)",
    count2 phrase!"number of lattice paths from $(0,0)$ to $(v,v)$" Const.latticePaths
      "the paths with unit steps right and up: the sequences of `m + n` steps of which `m` go right (`\\\\binom{m+n}{m}`)",
    { name := phrase!"multinomial coefficient of $v$ over $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real natP, dom1 .real natP, dom4 .real fun n a b c => and (natP c) (eq (add (add a b) c) n)],
      doc := "Mathlib `Nat.multinomial` of `a`, `b`, `c` (`n!/(a! b! c!)`), `a + b + c = n`",
      value := close <| lamR fun _ => lamR fun a => lamR fun b => lamR fun c => app (app2 (const Const.multinomial) a b) c }]

end Leanify.Counting
