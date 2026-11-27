import Leanify.Library.Core

/-! # Vocabulary: classical problems of probability

The answers to the classical problems, by their parameters (`We write $p_{365}(n)$ for the
probability of a shared birthday among $n$ people with $365$ days.`).

* notions: the probability of a shared birthday among `n` people with `d` equally likely days;
  the expected number of draws to collect `n` coupons; the ballot probability that `a` votes stay
  ahead of `b < a` votes throughout the count; the probability that a random permutation of `n`
  elements has no fixed point; the probability that Buffon's needle of length `ℓ` crosses a line
  of a grid with spacing `d ≥ ℓ`; the optimal cutoff and the success probability with cutoff `r`
  in the secretary problem; the expected number of runs of heads in `n` fair tosses.

The answers are constants, interpreted by the declarations of
`Leanify/Library/ClassicalProbabilityModel.lean`: probabilities and expectations in the
probability spaces of the problems (uniform finite spaces of outcomes, Mathlib's
`Measure.infinitePi` of independent uniform draws, the uniform position and angle of the
needle). Their closed forms (`1 - d!/((d-n)! d^n)`, `n H_n`, `(a-b)/(a+b)`, `∑_{k=0}^{n}
(-1)^k/k!`, `2ℓ/(π d)`, `(r/n) ∑_{k=r+1}^{n} 1/(k-1)`, `(n+1)/4`) are theorems, not
definitions; the optimal cutoff is the least cutoff with the greatest success probability
(about `n/e`, not always `⌊n/e⌋`). -/

namespace Leanify.ClassicalProbability
open Build Core

def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def fact (n : B) : B := app (prim .factorial) n
def zpow (x k : B) : B := app2 (prim .zpow) x k
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def finProd (a b : B) (body : B → B) : B := app (app (app (prim .finProd) a) b) (lamR body)
def pi : B := prim .pi
def exp (x : B) : B := app (prim (.realFn .exp)) x

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def birthday : Nat := 0
def coupons : Nat := 1
def ballot : Nat := 2
def derangementProb : Nat := 3
def buffon : Nat := 4
def optimalCutoff : Nat := 5
def success : Nat := 6
def expectedRuns : Nat := 7
end Const

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"p_{#1,#2}", w!"\\mathbb{E}T_{#}", w!"\\beta_{#1,#2}", w!"q_{#}", w!"\\operatorname{Buffon}_{#1,#2}",
    w!"r^{*}_{#}", w!"\\operatorname{succ}_{#1,#2}", w!"\\mathbb{E}R_{#}"]
  constLean := [w!"Leanify.ClassicalProbability.birthday", w!"Leanify.ClassicalProbability.coupons",
    w!"Leanify.ClassicalProbability.ballot", w!"Leanify.ClassicalProbability.derangementProb",
    w!"Leanify.ClassicalProbability.buffon", w!"Leanify.ClassicalProbability.optimalCutoff",
    w!"Leanify.ClassicalProbability.success", w!"Leanify.ClassicalProbability.expectedRuns"]
  modules := [w!"Leanify.Library.ClassicalProbabilityModel"]
  notions := [
    { name := phrase!"probability of a shared birthday among $v$ people with $v$ days", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real posInt],
      doc := "the share of the assignments `Fin n → Fin d` that are not injective (`1 - ∏_{i=0}^{n-1} (d-i)/d`)",
      value := .const Const.birthday },
    { name := phrase!"expected number of draws to collect $v$ coupons", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "the expectation of the first time every coupon has been drawn, for independent uniform draws (`n H_n`)",
      value := .const Const.coupons },
    { name := phrase!"ballot probability for $v$ and $v$ votes", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun a b => and (natP b) (lt b a)],
      doc := "the share of the orders of the count in which the winner with `a` votes is ahead throughout (`(a-b)/(a+b)`)",
      value := .const Const.ballot },
    { name := phrase!"probability of a derangement of $v$ elements", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "the share of the permutations without a fixed point (Mathlib `derangements`; `∑_{k=0}^{n} (-1)^k/k!`)",
      value := .const Const.derangementProb },
    { name := phrase!"probability that Buffon's needle of length $v$ crosses a line with spacing $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun l => lt (num 0) l, dom2 .real fun l d => le l d],
      doc := "for a uniform distance of the centre to the nearest line and a uniform angle (`2ℓ/(π d)` for `ℓ ≤ d`)",
      value := .const Const.buffon },
    { name := phrase!"optimal cutoff of the secretary problem with $v$ candidates", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "the least cutoff `r < n` with the greatest success probability (about `n/e`)",
      value := .const Const.optimalCutoff },
    { name := phrase!"success probability of the secretary problem with $v$ candidates and cutoff $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun n r => and (posInt r) (lt r n)],
      doc := "the share of the orders of the candidates in which rejecting the first `r` and taking the first better one takes the best (`(r/n) ∑_{k=r+1}^{n} 1/(k-1)`)",
      value := .const Const.success },
    { name := phrase!"expected number of runs of heads in $v$ fair tosses", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "the mean number of maximal blocks of heads over the `2^n` sequences (`(n+1)/4`)", value := .const Const.expectedRuns }]

end Leanify.ClassicalProbability
