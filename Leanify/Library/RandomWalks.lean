import Leanify.Library.Core

/-! # Vocabulary: random walks and gambler's ruin

The simple random walk on the integers with up-probability `p` (and `q = 1 - p`), started
at `k` and absorbed at `0` and `N`, and Brownian motion with drift, by their classical
formulas (`We write $r_k$ for the ruin probability from $k$ with target $N$ and
up-probability $p$.`).

* notions: the ruin probability `((q/p)^k - (q/p)^N)/(1 - (q/p)^N)` (`1 - k/N` for `p = 1/2`)
  and the probability of reaching `N` first; the expected duration of the game
  (`k(N-k)` for `p = 1/2`, `k/(q-p) - (N/(q-p))(1 - (q/p)^k)/(1 - (q/p)^N)` otherwise); the
  probability `\binom{n}{(n+x)/2} p^{(n+x)/2} q^{(n-x)/2}` that the walk is at `x` after `n`
  steps; the probability that Brownian motion with drift `μ` and variance `σ²` hits `a > 0`
  before `-b < 0` (`(1 - e^{2μb/σ²})/(e^{-2μa/σ²} - e^{2μb/σ²})`, `b/(a+b)` for `μ = 0`) and the
  expected exit time `ab/σ²` for `μ = 0`;
* the transition density of Brownian motion with drift `μ` and variance `σ²` at time `t > 0`
  (`x ↦ e^{-(x-μt)²/(2σ²t)}/√(2πσ²t)`).

Every meaning is a term of the core language. -/

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
def ratio (p : B) : B := div (sub (num 1) p) p
def ruin (k n p : B) : B :=
  cases (eq p (div (num 1) (num 2))) (sub (num 1) (div k n))
    (div (sub (zpow (ratio p) k) (zpow (ratio p) n)) (sub (num 1) (zpow (ratio p) n)))
def duration (k n p : B) : B :=
  cases (eq p (div (num 1) (num 2))) (mul k (sub n k))
    (sub (div k (sub (sub (num 1) p) p))
      (mul (div n (sub (sub (num 1) p) p)) (div (sub (num 1) (zpow (ratio p) k)) (sub (num 1) (zpow (ratio p) n)))))
def walk (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [none, dom2 .real fun k n => walkOk k n, dom1 .real unitOpen], doc,
    value := close <| lamR fun k => lamT .real (fun n => walkOk k n) fun n => lamT .real unitOpen fun p => body k n p }
def hitDom (a b s : B) : B := and (lt (num 0) a) (and (lt (num 0) b) (lt (num 0) s))
def hit (m s a b : B) : B :=
  cases (eq m (num 0)) (div b (add a b))
    (div (sub (num 1) (exp (div (mul (mul (num 2) m) b) s))) (sub (exp (neg (div (mul (mul (num 2) m) a) s))) (exp (div (mul (mul (num 2) m) b) s))))

def vocab : Vocab where
  notions := [
    walk phrase!"ruin probability from $v$ with target $v$ and up-probability $v$" ruin
      "the probability of reaching `0` before `N` from `k` (`1 - k/N` for `p = 1/2`)",
    walk phrase!"probability of reaching the target from $v$ with target $v$ and up-probability $v$" (fun k n p => sub (num 1) (ruin k n p))
      "the probability of reaching `N` before `0` from `k`",
    walk phrase!"expected duration from $v$ with target $v$ and up-probability $v$" duration
      "the expected number of steps until `0` or `N` is reached (`k(N-k)` for `p = 1/2`)",
    { name := phrase!"probability of being at $v$ after $v$ steps with up-probability $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt', dom1 .real fun n => and (isInt n) (le (num 0) n), dom1 .real fun p => and (le (num 0) p) (le p (num 1))],
      doc := "`\\binom{n}{(n+x)/2} p^{(n+x)/2} (1-p)^{(n-x)/2}` where `n + x` is even and `|x| ≤ n`, `0` otherwise",
      value := close <| lamT .real isInt' fun x => lamT .real (fun n => and (isInt n) (le (num 0) n)) fun n =>
        lamT .real (fun p => and (le (num 0) p) (le p (num 1))) fun p =>
          cases (and (isInt (div (add n x) (num 2))) (le (abs x) n))
            (mul (binom n (div (add n x) (num 2))) (mul (zpow p (div (add n x) (num 2))) (zpow (sub (num 1) p) (div (sub n x) (num 2)))))
            (num 0) },
    { name := phrase!"probability that Brownian motion with drift $v$ and variance $v$ hits $v$ before $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real fun s => lt (num 0) s, dom1 .real fun a => lt (num 0) a, dom1 .real fun c => lt c (num 0)],
      doc := "for `a > 0 > -b`: `(1 - e^{2μb/σ²})/(e^{-2μa/σ²} - e^{2μb/σ²})`, `b/(a+b)` for `μ = 0`",
      value := close <| lamR fun m => lamT .real (fun s => lt (num 0) s) fun s => lamT .real (fun a => lt (num 0) a) fun a =>
        lamT .real (fun c => lt c (num 0)) fun c => hit m s a (neg c) },
    { name := phrase!"expected exit time of Brownian motion with variance $v$ from $(v,v)$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s, none, dom2 .real fun a c => and (lt c (num 0)) (lt (num 0) a)],
      doc := "`ab/σ²` for the interval `(-b, a)`, started at `0`, without drift",
      value := close <| lamT .real (fun s => lt (num 0) s) fun s => lamR fun c => lamT .real (fun a => and (lt c (num 0)) (lt (num 0) a)) fun a =>
        div (mul a (neg c)) s },
    { name := phrase!"transition density of Brownian motion with drift $v$ and variance $v$ at time $v$", ty := .real ⟶ .real ⟶ .real ⟶ F,
      doms := [none, dom1 .real fun s => lt (num 0) s, dom1 .real fun t => lt (num 0) t],
      doc := "`x ↦ e^{-(x-μt)²/(2σ²t)}/√(2πσ²t)`",
      value := close <| lamR fun m => lamT .real (fun s => lt (num 0) s) fun s => lamT .real (fun t => lt (num 0) t) fun t => lamR fun x =>
        div (exp (neg (div (mul (sub x (mul m t)) (sub x (mul m t))) (mul (mul (num 2) s) t)))) (sqrt (mul (mul (mul (num 2) pi) s) t)) }]

end Leanify.RandomWalks
