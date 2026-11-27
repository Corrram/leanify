import Leanify.Library.Core

/-! # Vocabulary: random walks and gambler's ruin

The simple random walk on the integers with up-probability `p` (and `q = 1 - p`), started
at `k` and absorbed at `0` and `N`, and Brownian motion with drift (`We write $r_k$ for the
ruin probability from $k$ with target $N$ and up-probability $p$.`).

* notions: the ruin probability and the probability of reaching `N` first; the expected
  duration of the game; the probability that the walk is at `x` after `n` steps; the
  probability that Brownian motion with drift `μ` and variance `σ²` hits `a > 0` before
  `c < 0` and its expected exit time from `(c, a)` without drift;
* the transition density of Brownian motion with drift `μ` and variance `σ²` at time `t > 0`.

The quantities are constants, interpreted by the declarations of
`Leanify/Library/RandomWalksModel.lean`: the probabilities and expectations of the events and
exit times of the walk of independent steps (Mathlib `Measure.infinitePi`), and of `μt + σB_t`
for a Brownian motion `B` (Mathlib `IsBrownianReal`) on every probability space with one; the
transition density is the Gaussian density of `N(μt, σ²t)` (Mathlib `gaussianPDFReal`). The
classical formulas (`((q/p)^k - (q/p)^N)/(1 - (q/p)^N)`, `k(N-k)`, `\binom{n}{(n+x)/2}
p^{(n+x)/2} q^{(n-x)/2}`, `(1 - e^{2μb/σ²})/(e^{-2μa/σ²} - e^{2μb/σ²})`, `ab/σ²`) are theorems,
not definitions. A Brownian motion must exist on some probability space for its quantities to
be meaningful. -/

namespace Leanify.RandomWalks
open Build Core

abbrev F : Ty := Ty.rfun

def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def exp (x : B) : B := app (prim (.realFn .exp)) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def pi : B := prim .pi
def isInt' (x : B) : B := isInt x
def unitOpen (p : B) : B := and (lt (num 0) p) (lt p (num 1))
def walkOk (k n : B) : B := and (isInt n) (and (le (num 1) n) (and (isInt k) (and (le (num 0) k) (le k n))))
/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def ruin : Nat := 0
def reachTarget : Nat := 1
def duration : Nat := 2
def atAfter : Nat := 3
def brownianHit : Nat := 4
def brownianExit : Nat := 5
def transitionDensity : Nat := 6
end Const

def walk (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [none, dom2 .real fun k n => walkOk k n, dom1 .real unitOpen], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real ⟶ F]
  constNames := [w!"r_{#1}(#2,#3)", w!"w_{#1}(#2,#3)", w!"D_{#1}(#2,#3)", w!"P(S_{#2}=#1)_{#3}", w!"\\operatorname{hit}",
    w!"\\mathbb{E}\\tau(#1,#2,#3)", w!"\\varphi"]
  constLean := [w!"Leanify.RandomWalks.ruin", w!"Leanify.RandomWalks.reachTarget", w!"Leanify.RandomWalks.duration",
    w!"Leanify.RandomWalks.atAfter", w!"Leanify.RandomWalks.brownianHit", w!"Leanify.RandomWalks.brownianExit",
    w!"Leanify.RandomWalks.transitionDensity"]
  modules := [w!"Leanify.Library.RandomWalksModel"]
  notions := [
    walk phrase!"ruin probability from $v$ with target $v$ and up-probability $v$" Const.ruin
      "the probability of reaching `0` before `N` from `k` (`((q/p)^k - (q/p)^N)/(1 - (q/p)^N)`, `1 - k/N` for `p = 1/2`)",
    walk phrase!"probability of reaching the target from $v$ with target $v$ and up-probability $v$" Const.reachTarget
      "the probability of reaching `N` before `0` from `k`",
    walk phrase!"expected duration from $v$ with target $v$ and up-probability $v$" Const.duration
      "the expected number of steps until `0` or `N` is reached (`k(N-k)` for `p = 1/2`)",
    { name := phrase!"probability of being at $v$ after $v$ steps with up-probability $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt', dom1 .real fun n => and (isInt n) (le (num 0) n), dom1 .real fun p => and (le (num 0) p) (le p (num 1))],
      doc := "the probability that the walk from `0` is at `x` after `n` steps (`\\binom{n}{(n+x)/2} p^{(n+x)/2} (1-p)^{(n-x)/2}` where `n + x` is even and `|x| ≤ n`, `0` otherwise)",
      value := .const Const.atAfter },
    { name := phrase!"probability that Brownian motion with drift $v$ and variance $v$ hits $v$ before $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real fun s => lt (num 0) s, dom1 .real fun a => lt (num 0) a, dom1 .real fun c => lt c (num 0)],
      doc := "of `μt + σB_t` reaching `a > 0` before `c < 0` (`(1 - e^{2μb/σ²})/(e^{-2μa/σ²} - e^{2μb/σ²})` for `c = -b`, `b/(a+b)` for `μ = 0`)",
      value := .const Const.brownianHit },
    { name := phrase!"expected exit time of Brownian motion with variance $v$ from $(v,v)$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s, none, dom2 .real fun a c => and (lt c (num 0)) (lt (num 0) a)],
      doc := "of `σB_t` from the interval `(c, a)`, started at `0` (`ab/σ²` for `c = -b`)",
      value := .const Const.brownianExit },
    { name := phrase!"transition density of Brownian motion with drift $v$ and variance $v$ at time $v$", ty := .real ⟶ .real ⟶ .real ⟶ F,
      doms := [none, dom1 .real fun s => lt (num 0) s, dom1 .real fun t => lt (num 0) t],
      doc := "the Gaussian density of `N(μt, σ²t)`, the law of `μt + σB_t` (Mathlib `gaussianPDFReal`; `x ↦ e^{-(x-μt)²/(2σ²t)}/√(2πσ²t)`)",
      value := .const Const.transitionDensity }]

end Leanify.RandomWalks
