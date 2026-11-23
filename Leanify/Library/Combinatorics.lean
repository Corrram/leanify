import Leanify.Library.Core

/-! # Vocabulary: enumerative combinatorics

Counting numbers of nonnegative integers: Fibonacci, Catalan, Bell, harmonic and triangular
numbers, derangements, partitions of integers and of sets, permutations with a given number
of cycles. Each is a notion with its arguments (`the $n$th Catalan number`, `the number of
partitions of a set of $n$ elements into $k$ blocks`), defined for nonnegative integers; an
article fixes its notation itself (`We write $C_n$ for the $n$th Catalan number.`).

The numbers of Mathlib are constants, interpreted by the declarations of
`Leanify/Library/CombinatoricsModel.lean` (`Nat.fib`, `catalan`, `Nat.bell`,
`numDerangements`, `Nat.stirlingFirst`, `Nat.stirlingSecond`, `Nat.Partition`); the
harmonic and triangular numbers are terms of the core language. Factorials and binomial
coefficients (`n!`, `\binom{n}{k}`) are in the core. -/

namespace Leanify.Combinatorics
open Build Core

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def fib : Nat := 0
def catalan : Nat := 1
def bell : Nat := 2
def derangements : Nat := 3
def partitions : Nat := 4
def stirling2 : Nat := 5
def stirling1 : Nat := 6
end Const
open Const

def natDom : Option Tm := some nonnegInt

/-- `H_n = ∑_{k=1}^{n} 1/k`. -/
def harmonic : Tm := close <| lamR fun n =>
  app (app (app (prim .finSum) (num 1)) n) (lamR fun k => div (num 1) k)

/-- `n(n+1)/2`. -/
def triangular : Tm := close <| lamR fun n => div (mul n (add n (num 1))) (num 2)

/-- A notion of one nonnegative integer. -/
def ofNat (name : Phrase) (value : Tm) (doc : String) : Notion :=
  { name, value, ty := .real ⟶ .real, doms := [natDom], doc }

/-- A notion of two nonnegative integers. -/
def ofNat2 (name : Phrase) (value : Tm) (doc : String) : Notion :=
  { name, value, ty := .real ⟶ .real ⟶ .real, doms := [natDom, natDom], doc }

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real]
  constNames := [w!"\\operatorname{Fib}", w!"\\operatorname{Cat}", w!"\\operatorname{Bell}",
    w!"\\operatorname{D}", w!"\\operatorname{p}", w!"S(#1,#2)", w!"c(#1,#2)"]
  constLean := [w!"Leanify.Combinatorics.fib", w!"Leanify.Combinatorics.catalan",
    w!"Leanify.Combinatorics.bell", w!"Leanify.Combinatorics.derangements",
    w!"Leanify.Combinatorics.partitions", w!"Leanify.Combinatorics.stirling2",
    w!"Leanify.Combinatorics.stirling1"]
  modules := [w!"Leanify.Library.CombinatoricsModel"]
  notions := [
    ofNat phrase!"$v$th Fibonacci number" (.const fib)
      "`F_0 = 0`, `F_1 = 1`, `F_{n+2} = F_{n+1} + F_n` (Mathlib `Nat.fib`)",
    ofNat phrase!"$v$th Catalan number" (.const catalan)
      "`C_n = \\binom{2n}{n}/(n+1)` (Mathlib `catalan`)",
    ofNat phrase!"$v$th Bell number" (.const bell)
      "the number of partitions of a set of `n` elements (Mathlib `Nat.bell`)",
    ofNat phrase!"$v$th harmonic number" harmonic "`H_n = ∑_{k=1}^{n} 1/k` (Mathlib `harmonic`)",
    ofNat phrase!"$v$th triangular number" triangular "`n(n+1)/2`",
    ofNat phrase!"number of derangements of $v$ elements" (.const derangements)
      "the permutations of `n` elements without fixed points (Mathlib `numDerangements`)",
    ofNat phrase!"number of partitions of $v$" (.const partitions)
      "the ways of writing `n` as a sum of positive integers, without order (Mathlib `Nat.Partition`)",
    ofNat phrase!"number of partitions of a set of $v$ elements" (.const bell)
      "the Bell number (Mathlib `Nat.bell`)",
    ofNat2 phrase!"number of partitions of a set of $v$ elements into $v$ blocks" (.const stirling2)
      "the Stirling number of the second kind (Mathlib `Nat.stirlingSecond`)",
    ofNat2 phrase!"Stirling number of the second kind for $v$ and $v$" (.const stirling2)
      "the partitions of a set of `n` elements into `k` blocks (Mathlib `Nat.stirlingSecond`)",
    ofNat2 phrase!"number of permutations of $v$ elements with $v$ cycles" (.const stirling1)
      "the unsigned Stirling number of the first kind (Mathlib `Nat.stirlingFirst`)",
    ofNat2 phrase!"Stirling number of the first kind for $v$ and $v$" (.const stirling1)
      "unsigned: the permutations of `n` elements with `k` cycles (Mathlib `Nat.stirlingFirst`)"]

end Leanify.Combinatorics
