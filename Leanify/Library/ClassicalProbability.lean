import Leanify.Library.Core

/-! # Vocabulary: classical problems of probability

The answers to the classical problems, by their parameters (`We write $p_{365}(n)$ for the
probability of a shared birthday among $n$ people with $365$ days.`).

* notions: the probability of a shared birthday among `n` people with `d` equally likely days
  (`1 - d!/((d-n)! d^n)`, `1` for `n > d`); the expected number of draws to collect `n` coupons
  (`n H_n`); the ballot probability that `a` votes stay ahead of `b < a` votes throughout the
  count (`(a-b)/(a+b)`); the probability that a random permutation of `n` elements has no fixed
  point (`∑_{k=0}^{n} (-1)^k/k!`); the probability that Buffon's needle of length `ℓ` crosses a
  line of a grid with spacing `d ≥ ℓ` (`2ℓ/(π d)`); the optimal cutoff `⌊n/e⌋` and the success
  probability `(r/n) ∑_{k=r+1}^{n} 1/(k-1)` with cutoff `r` in the secretary problem; the
  expected number of fixed points of a random permutation (`1`); the expected number of runs of
  heads in `n` fair tosses (`(n+1)/4`).

Every meaning is a term of the core language. -/

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

def vocab : Vocab where
  notions := [
    { name := phrase!"probability of a shared birthday among $v$ people with $v$ days", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real posInt],
      doc := "`1 - ∏_{i=0}^{n-1} (d-i)/d`, which is `1` for `n > d`",
      value := close <| lamT .real natP fun n => lamT .real posInt fun d =>
        sub (num 1) (finProd (num 0) (sub n (num 1)) fun i => div (sub d i) d) },
    { name := phrase!"expected number of draws to collect $v$ coupons", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`n H_n = n ∑_{k=1}^{n} 1/k`",
      value := close <| lamT .real posInt fun n => mul n (finSum (num 1) n fun k => div (num 1) k) },
    { name := phrase!"ballot probability for $v$ and $v$ votes", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun a b => and (natP b) (lt b a)],
      doc := "`(a-b)/(a+b)`: the winner with `a` votes is ahead throughout the count",
      value := close <| lamT .real posInt fun a => lamT .real (fun b => and (natP b) (lt b a)) fun b => div (sub a b) (add a b) },
    { name := phrase!"probability of a derangement of $v$ elements", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "`∑_{k=0}^{n} (-1)^k/k!`: no fixed point in a uniformly random permutation",
      value := close <| lamT .real natP fun n => finSum (num 0) n fun k => div (zpow (neg (num 1)) k) (fact k) },
    { name := phrase!"probability that Buffon's needle of length $v$ crosses a line with spacing $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun l => lt (num 0) l, dom2 .real fun l d => le l d],
      doc := "`2ℓ/(π d)` for `ℓ ≤ d`",
      value := close <| lamT .real (fun l => lt (num 0) l) fun l => lamT .real (fun d => le l d) fun d =>
        div (mul (num 2) l) (mul pi d) },
    { name := phrase!"optimal cutoff of the secretary problem with $v$ candidates", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`⌊n/e⌋`, asymptotically optimal",
      value := close <| lamT .real posInt fun n => floor (div n (exp (num 1))) },
    { name := phrase!"success probability of the secretary problem with $v$ candidates and cutoff $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun n r => and (posInt r) (lt r n)],
      doc := "`(r/n) ∑_{k=r+1}^{n} 1/(k-1)`, rejecting the first `r` candidates",
      value := close <| lamT .real posInt fun n => lamT .real (fun r => and (posInt r) (lt r n)) fun r =>
        mul (div r n) (finSum (add r (num 1)) n fun k => div (num 1) (sub k (num 1))) },
    { name := phrase!"expected number of runs of heads in $v$ fair tosses", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`(n+1)/4`", value := close <| lamT .real posInt fun n => div (add n (num 1)) (num 4) }]

end Leanify.ClassicalProbability
