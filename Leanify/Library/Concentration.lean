import Leanify.Library.Core

/-! # Vocabulary: concentration inequalities and sample complexity

The right-hand sides of the classical tail bounds, as quantities (`We write $B_H(n,t)$ for
the Hoeffding bound for $n$ observations in an interval of length $\ell$ at deviation $t$.`),
and the sample sizes they give, as in learning theory and statistics.

* notions: the Markov bound `μ/a`; the Chebyshev bound `σ²/t²`; the one-sided Cantelli bound
  `σ²/(σ² + t²)`; the Hoeffding bound `2 exp(-2nt²/ℓ²)` for the mean of `n` observations in an
  interval of length `ℓ`; the Bernstein bound `2 exp(-nt²/(2σ² + 2ℓt/3))` for variance `σ²` and
  observations bounded by `ℓ` around their mean; the multiplicative Chernoff bound
  `exp(-δ²μ/3)` for `0 < δ ≤ 1`; McDiarmid's bound `2 exp(-2t²/(n c²))` for bounded differences
  `c`; the Hoeffding sample size `⌈ℓ² log(2/δ)/(2ε²)⌉`; the sample complexity
  `⌈(log k + log(1/δ))/ε⌉` of a finite hypothesis class with `k` hypotheses (realizable case)
  and `⌈(log k + log(2/δ))/(2ε²)⌉` (agnostic case).

Every meaning is a term of the core language. -/

namespace Leanify.Concentration
open Build Core

def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def ceil (x : B) : B := app (prim .ceil) x
def unitOpen (d : B) : B := and (lt (num 0) d) (lt d (num 1))
def n2 (name : Phrase) (d1 d2 : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom1 .real d2], doc,
    value := close <| lamT .real d1 fun a => lamT .real d2 fun b => body a b }
def n3 (name : Phrase) (d1 d2 d3 : B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom1 .real d2, dom1 .real d3], doc,
    value := close <| lamT .real d1 fun a => lamT .real d2 fun b => lamT .real d3 fun c => body a b c }
def nonneg (x : B) : B := le (num 0) x

def vocab : Vocab where
  notions := [
    n2 phrase!"Markov bound for the mean $v$ at the level $v$" nonneg pos (fun m a => div m a)
      "`μ/a`: `P(X ≥ a) ≤ μ/a` for `X ≥ 0`",
    n2 phrase!"Chebyshev bound for the variance $v$ at the deviation $v$" nonneg pos (fun s t => div s (mul t t))
      "`σ²/t²`: `P(|X - μ| ≥ t) ≤ σ²/t²`",
    n2 phrase!"Cantelli bound for the variance $v$ at the deviation $v$" nonneg pos (fun s t => div s (add s (mul t t)))
      "`σ²/(σ² + t²)`: `P(X - μ ≥ t) ≤ σ²/(σ² + t²)`",
    n3 phrase!"Hoeffding bound for $v$ observations in an interval of length $v$ at the deviation $v$" posInt pos pos
      (fun n l t => mul (num 2) (exp (neg (div (mul (mul (num 2) n) (mul t t)) (mul l l)))))
      "`2 exp(-2nt²/ℓ²)`: `P(|X̄ - μ| ≥ t)` for `n` independent observations in an interval of length `ℓ`",
    { name := phrase!"Bernstein bound for $v$ observations with variance $v$ and range $v$ at the deviation $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real nonneg, dom1 .real pos, dom1 .real pos],
      doc := "`2 exp(-nt²/(2σ² + 2ℓt/3))`, for `|X_i - μ| ≤ ℓ`",
      value := close <| lamT .real posInt fun n => lamT .real nonneg fun s => lamT .real pos fun l => lamT .real pos fun t =>
        mul (num 2) (exp (neg (div (mul n (mul t t)) (add (mul (num 2) s) (div (mul (num 2) (mul l t)) (num 3)))))) },
    n2 phrase!"Chernoff bound for the mean $v$ at the relative deviation $v$" pos (fun d => and (lt (num 0) d) (le d (num 1)))
      (fun m d => exp (neg (div (mul (mul d d) m) (num 3))))
      "`exp(-δ²μ/3)`: `P(X ≥ (1+δ)μ)` for a sum of independent Bernoulli variables, `0 < δ ≤ 1`",
    n3 phrase!"McDiarmid bound for $v$ variables with bounded differences $v$ at the deviation $v$" posInt pos pos
      (fun n c t => mul (num 2) (exp (neg (div (mul (num 2) (mul t t)) (mul n (mul c c))))))
      "`2 exp(-2t²/(n c²))`",
    n3 phrase!"Hoeffding sample size for an interval of length $v$, accuracy $v$ and confidence parameter $v$" pos pos unitOpen
      (fun l e d => ceil (div (mul (mul l l) (log (div (num 2) d))) (mul (num 2) (mul e e))))
      "`⌈ℓ² log(2/δ)/(2ε²)⌉` observations for `P(|X̄ - μ| ≥ ε) ≤ δ`",
    n3 phrase!"realizable sample complexity of $v$ hypotheses with accuracy $v$ and confidence parameter $v$" posInt pos unitOpen
      (fun k e d => ceil (div (add (log k) (log (div (num 1) d))) e))
      "`⌈(log k + log(1/δ))/ε⌉`, a consistent learner over a finite class",
    n3 phrase!"agnostic sample complexity of $v$ hypotheses with accuracy $v$ and confidence parameter $v$" posInt pos unitOpen
      (fun k e d => ceil (div (add (log k) (log (div (num 2) d))) (mul (num 2) (mul e e))))
      "`⌈(log k + log(2/δ))/(2ε²)⌉`, empirical risk minimization over a finite class"]

end Leanify.Concentration
