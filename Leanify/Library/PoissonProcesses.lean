import Leanify.Library.Core

/-! # Vocabulary: Poisson processes

Arrival counts and waiting times of a homogeneous Poisson process, by its rate (`We write
$p(k,t,\lambda)$ for the probability of $k$ arrivals by time $t$ at rate $\lambda$.`). The Poisson
distribution as an object is in the field `distributions`.

* notions: the probability `e^{-λt}(λt)^k/k!` of `k` arrivals by time `t`; the probability
  `1 - e^{-λt}` of at least one arrival; the expected waiting time `k/λ` for the `k`th arrival;
  the probability `∑_{j<k} e^{-λt}(λt)^j/j!` that the `k`th arrival comes after `t`; the rate `pλ`
  of a thinned process; the mean `λtμ` and variance `λt(σ² + μ²)` of a compound Poisson sum.

Every meaning is a term of the core language. -/

namespace Leanify.PoissonProcesses
open Build Core

def pos (x : B) : B := lt (num 0) x
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def exp (x : B) : B := app (prim (.realFn .exp)) x
def zpow (x k : B) : B := app2 (prim .zpow) x k
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def pmf (k t l : B) : B := div (mul (exp (neg (mul l t))) (zpow (mul l t) k)) (fact k)
def nonneg (t : B) : B := le (num 0) t

def vocab : Vocab where
  notions := [
    { name := phrase!"probability of $v$ arrivals by time $v$ at rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ t => nonneg t, dom3 .real fun _ _ l => pos l], doc := "`e^{-λt}(λt)^k/k!`",
      value := close <| lamT .real natP fun k => lamT .real nonneg fun t => lamT .real pos fun l => pmf k t l },
    { name := phrase!"probability of an arrival by time $v$ at rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nonneg, dom2 .real fun _ l => pos l], doc := "`1 - e^{-λt}`",
      value := close <| lamT .real nonneg fun t => lamT .real pos fun l => sub (num 1) (exp (neg (mul l t))) },
    { name := phrase!"expected waiting time for the $v$th arrival at rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ l => pos l], doc := "`k/λ` (Erlang)",
      value := close <| lamT .real posInt fun k => lamT .real pos fun l => div k l },
    { name := phrase!"probability that the $v$th arrival comes after time $v$ at rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ t => nonneg t, dom3 .real fun _ _ l => pos l],
      doc := "`∑_{j=0}^{k-1} e^{-λt}(λt)^j/j!`",
      value := close <| lamT .real posInt fun k => lamT .real nonneg fun t => lamT .real pos fun l =>
        finSum (num 0) (sub k (num 1)) fun j => pmf j t l },
    { name := phrase!"rate of the process with rate $v$ thinned with probability $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ p => and (le (num 0) p) (le p (num 1))], doc := "`pλ`: each arrival kept with probability `p`",
      value := close <| lamT .real pos fun l => lamT .real (fun p => and (le (num 0) p) (le p (num 1))) fun p => mul p l },
    { name := phrase!"mean of the compound Poisson sum at time $v$ with rate $v$ and jump mean $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nonneg, dom2 .real fun _ l => pos l, none], doc := "`λtμ`",
      value := close <| lamT .real nonneg fun t => lamT .real pos fun l => lamR fun m => mul l (mul t m) },
    { name := phrase!"variance of the compound Poisson sum at time $v$ with rate $v$, jump mean $v$ and jump variance $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nonneg, dom2 .real fun _ l => pos l, none, dom4 .real fun _ _ _ v => le (num 0) v], doc := "`λt(σ² + μ²)`",
      value := close <| lamT .real nonneg fun t => lamT .real pos fun l => lamR fun m => lamT .real (fun v => le (num 0) v) fun v =>
        mul l (mul t (add v (mul m m))) }]

end Leanify.PoissonProcesses
