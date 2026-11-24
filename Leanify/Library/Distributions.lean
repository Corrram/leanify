import Leanify.Library.Core

/-! # Vocabulary: probability distributions on ℕ₀

A probability distribution on `ℕ₀ = {0, 1, 2, …}` is read as its weights: a real
function `x` with `x(k) ≥ 0` at the natural numbers, `x(t) = 0` elsewhere, and
`∑_{k=0}^∞ x(k) = 1`. The standard distributions are notions with parameters:

* `Poisson distribution with mean $λ$` (`λ ≥ 0`): `e^{-λ} λ^k / k!`;
* `binomial distribution with parameters $n$ and $p$` (`n ∈ ℕ₀`, `p ∈ [0,1]`):
  `\binom{n}{k} p^k (1-p)^{n-k}` for `k ≤ n`;
* `negative binomial distribution with parameters $r$ and $p$` (`r ∈ ℕ`, `r ≥ 1`,
  `p ∈ (0,1]`): `\binom{k+r-1}{k} p^r (1-p)^k`, the number of failures before the
  `r`-th success;
* `point mass at $m$` (`m ∈ ℕ₀`);
* `mean of $x$`: `∑_k k x(k)`, defined when the series converges;
* the geometric, Bernoulli, discrete uniform and hypergeometric distributions, the variance
  of a distribution and its probability generating function (`More`).

Everything is a term of the core language (series, integer powers, factorials and
binomial coefficients of the core prelude): the vocabulary has no constants of
its own, and needs no model beyond the core one. An article declares its
notation for these phrases itself: `We write $\mathcal P(\mathbb N_0)$ for the set
of probability distributions on $\mathbb N_0$.`, `We write
$\mathrm{Poi}(\lambda)$ for the Poisson distribution with mean $\lambda$.` -/

namespace Leanify.Distributions

def isNat (t : Tm) : Tm := .app (.prim .isNat) t
def zpow (a b : Tm) : Tm := .app (.app (.prim .zpow) a) b
def factorial (t : Tm) : Tm := .app (.prim .factorial) t
def binom (a b : Tm) : Tm := .app (.app (.prim .binom) a) b
def exp (t : Tm) : Tm := .app (.prim (.realFn .exp)) t

/-- The weights `k ↦ x(k)` of `x` (here `loc 1`) over `k ∈ ℕ₀`, as a series. -/
def weightsOf (x : Tm) : Tm := .lam .real (.and (isNat (.loc 0)) (.le (.num 0) (.loc 0))) (.app x (.loc 0))

/-- `x` (the bound function) is a probability distribution on `ℕ₀`. -/
def isDistribution : Tm :=
  .lam Ty.rfun .tt
    (.and (.all .real (.and (.imp (isNat (.loc 0)) (.le (.num 0) (.app (.loc 1) (.loc 0))))
                            (.imp (.not (isNat (.loc 0))) (.eq (.app (.loc 1) (.loc 0)) (.num 0)))))
      (.and (.app (.app (.prim .seriesConv) (.num 0)) (weightsOf (.loc 1)))
        (.eq (.app (.app (.prim .series) (.num 0)) (weightsOf (.loc 1))) (.num 1))))

/-- Weights `k ↦ w(k)` at the natural numbers `k` with `cond`, `0` elsewhere
(`k` is `loc 0`). -/
def weights (cond w : Tm) : Tm := .lam .real .tt (.cases (.and (isNat (.loc 0)) cond) w (.num 0))

/-- `λ ↦ (k ↦ e^{-λ} λ^k / k!)`. -/
def poisson : Tm :=
  .lam .real .tt (weights .tt
    (.div (.mul (exp (.neg (.loc 1))) (zpow (.loc 1) (.loc 0))) (factorial (.loc 0))))

/-- `n ↦ p ↦ (k ↦ \binom{n}{k} p^k (1-p)^{n-k})` for `k ≤ n`. -/
def binomial : Tm :=
  .lam .real .tt (.lam .real .tt (weights (.le (.loc 0) (.loc 2))
    (.mul (binom (.loc 2) (.loc 0))
      (.mul (zpow (.loc 1) (.loc 0)) (zpow (.sub (.num 1) (.loc 1)) (.sub (.loc 2) (.loc 0)))))))

/-- `r ↦ p ↦ (k ↦ \binom{k+r-1}{k} p^r (1-p)^k)`. -/
def negBinomial : Tm :=
  .lam .real .tt (.lam .real .tt (weights .tt
    (.mul (binom (.sub (.add (.loc 0) (.loc 2)) (.num 1)) (.loc 0))
      (.mul (zpow (.loc 1) (.loc 2)) (zpow (.sub (.num 1) (.loc 1)) (.loc 0))))))

/-- `m ↦ (k ↦ 1 if k = m, else 0)`. -/
def pointMass : Tm := .lam .real .tt (weights (.eq (.loc 0) (.loc 1)) (.num 1))

/-- `x ↦ ∑_k k x(k)`, defined when the series converges. -/
def mean : Tm :=
  let terms := Tm.lam .real (.and (isNat (.loc 0)) (.le (.num 0) (.loc 0))) (.mul (.loc 0) (.app (.loc 1) (.loc 0)))
  .lam Ty.rfun .tt (.guard (.app (.app (.prim .seriesConv) (.num 0)) terms)
    (.app (.app (.prim .series) (.num 0)) terms))

def dom (p : Tm) : Option Tm := some (.lam .real .tt p)

/-! ### More distributions, the variance and the generating function (in `Build` terms) -/

namespace More
open Build

def nat (k : B) : B := and (Build.isInt k) (le (num 0) k)
def zp (x k : B) : B := app2 (prim .zpow) x k
def bin (n k : B) : B := app2 (prim .binom) n k
/-- Weights `k ↦ w(k)` at the natural numbers with `c k`, `0` elsewhere. -/
def wts (c w : B → B) : B := lamR fun k => cases (and (nat k) (c k)) (w k) (num 0)
def conv (t : B) : B := app2 (prim .seriesConv) (num 0) t
def ser (t : B) : B := app2 (prim .series) (num 0) t
def momentTerms (j x : B) : B := lamR fun k => mul (zp k j) (app x k)
def prob (p : B) : B := and (le (num 0) p) (le p (num 1))
def posProb (p : B) : B := and (lt (num 0) p) (le p (num 1))
def posInt (n : B) : B := and (Build.isInt n) (lt (num 0) n)
def natP (n : B) : B := nat n
def isDist (x : B) : B := app (lift isDistribution) x
def secondMoment (x : B) : B := conv (momentTerms (num 2) x)
def meanB (x : B) : B := ser (momentTerms (num 1) x)

def notions : List Notion := [
  { name := phrase!"geometric distribution with parameter $v$", ty := .real ⟶ Ty.rfun,
    doms := [dom1 .real posProb], doc := "`p(1-p)^k`, the number of failures before the first success; `0 < p ≤ 1`",
    value := close <| lamT .real posProb fun p => wts (fun _ => tt) fun k => mul p (zp (sub (num 1) p) k) },
  { name := phrase!"Bernoulli distribution with parameter $v$", ty := .real ⟶ Ty.rfun,
    doms := [dom1 .real prob], doc := "`1 - p` at `0`, `p` at `1`; `0 ≤ p ≤ 1`",
    value := close <| lamT .real prob fun p => wts (fun k => le k (num 1)) fun k => cases (eq k (num 0)) (sub (num 1) p) p },
  { name := phrase!"discrete uniform distribution on $v$ points", ty := .real ⟶ Ty.rfun,
    doms := [dom1 .real posInt], doc := "`1/n` at `0, …, n-1`; `n ≥ 1`",
    value := close <| lamT .real posInt fun n => wts (fun k => lt k n) fun _ => div (num 1) n },
  { name := phrase!"hypergeometric distribution with parameters $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ Ty.rfun,
    doms := [dom1 .real natP, dom2 .real fun nn kk => and (nat kk) (le kk nn), dom3 .real fun nn _ n => and (nat n) (le n nn)],
    doc := "`\\binom{K}{k}\\binom{N-K}{n-k}/\\binom{N}{n}`: `k` marked in a sample of `n` from `N` with `K` marked",
    value := close <| lamT .real natP fun nn => lamT .real (fun kk => and (nat kk) (le kk nn)) fun kk =>
      lamT .real (fun n => and (nat n) (le n nn)) fun n =>
        wts (fun k => and (le k kk) (le k n)) fun k => div (mul (bin kk k) (bin (sub nn kk) (sub n k))) (bin nn n) },
  { name := phrase!"variance of the distribution $v$", ty := Ty.rfun ⟶ .real,
    doms := [dom1 Ty.rfun fun x => and (isDist x) (secondMoment x)],
    doc := "`∑ k² x(k) - (∑ k x(k))²`, where `∑ k² x(k)` converges",
    value := close <| lamT Ty.rfun (fun x => and (isDist x) (secondMoment x)) fun x =>
      sub (ser (momentTerms (num 2) x)) (mul (meanB x) (meanB x)) },
  { name := phrase!"probability generating function of $v$", ty := Ty.rfun ⟶ Ty.rfun,
    doms := [dom1 Ty.rfun isDist, dom2 .real fun x s => conv (lamR fun k => mul (app x k) (zp s k))],
    doc := "`s ↦ ∑ x(k) s^k`, where the series converges",
    value := close <| lamT Ty.rfun isDist fun x => lamT .real (fun s => conv (lamR fun k => mul (app x k) (zp s k))) fun s =>
      ser (lamR fun k => mul (app x k) (zp s k)) }]

end More

def vocab : Vocab where
  nouns := [
    { sing := phrase!"probability distribution $v$ on $\\mathbb{N}_0$",
      plural := phrase!"probability distributions $v$ on $\\mathbb{N}_0$", ty := Ty.rfun, pred := isDistribution,
      doc := "weights `x(k) ≥ 0` at `k ∈ ℕ₀`, `0` elsewhere, `∑ x(k) = 1` (Mathlib `PMF ℕ`)" },
    { sing := phrase!"probability distribution $v$ on $\\mathbb{N}$",
      plural := phrase!"probability distributions $v$ on $\\mathbb{N}$", ty := Ty.rfun, pred := isDistribution,
      doc := "as on `ℕ₀` (`ℕ` includes 0, as in Mathlib)" },
    { sing := phrase!"distribution $v$ on $\\mathbb{N}_0$",
      plural := phrase!"distributions $v$ on $\\mathbb{N}_0$", ty := Ty.rfun, pred := isDistribution,
      doc := "a probability distribution on `ℕ₀`" }]
  notions := [
    { name := phrase!"Poisson distribution with mean $v$", value := poisson, ty := .real ⟶ Ty.rfun,
      doms := [dom (.le (.num 0) (.loc 0))], doc := "`k ↦ e^{-λ} λ^k / k!`, `λ ≥ 0` (Mathlib `poissonPMF`)" },
    { name := phrase!"binomial distribution with parameters $v$ and $v$", value := binomial,
      ty := .real ⟶ .real ⟶ Ty.rfun,
      doms := [dom (isNat (.loc 0)), dom (.and (.le (.num 0) (.loc 0)) (.le (.loc 0) (.num 1)))],
      doc := "`k ↦ C(n,k) p^k (1-p)^{n-k}` for `k ≤ n` (Mathlib `PMF.binomial`)" },
    { name := phrase!"negative binomial distribution with parameters $v$ and $v$", value := negBinomial,
      ty := .real ⟶ .real ⟶ Ty.rfun,
      doms := [dom (.and (isNat (.loc 0)) (.le (.num 1) (.loc 0))),
        dom (.and (.lt (.num 0) (.loc 0)) (.le (.loc 0) (.num 1)))],
      doc := "`k ↦ C(k+r-1,k) p^r (1-p)^k`: failures before the `r`-th success" },
    { name := phrase!"point mass at $v$", value := pointMass, ty := .real ⟶ Ty.rfun,
      doms := [dom (isNat (.loc 0))], doc := "`k ↦ 1` if `k = m`, else `0` (Mathlib `PMF.pure`)" },
    { name := phrase!"mean of the distribution $v$", value := mean, ty := Ty.rfun ⟶ .real, doms := [none],
      doc := "`∑ k x(k)`, defined when the series converges" },
    { name := phrase!"mean of $v$", value := mean, ty := Ty.rfun ⟶ .real, doms := [none],
      doc := "`∑ k x(k)`, defined when the series converges" }] ++ More.notions

/-- The core vocabulary followed by this one. -/
def withCore : Vocab := Vocab.core ++ vocab

end Leanify.Distributions
