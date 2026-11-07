import Leanify.Vocab

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
* `mean of $x$`: `∑_k k x(k)`, defined when the series converges.

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

def vocab : Vocab where
  nouns := [
    { sing := phrase!"probability distribution $v$ on $\\mathbb{N}_0$",
      plural := phrase!"probability distributions $v$ on $\\mathbb{N}_0$", ty := Ty.rfun, pred := isDistribution },
    { sing := phrase!"probability distribution $v$ on $\\mathbb{N}$",
      plural := phrase!"probability distributions $v$ on $\\mathbb{N}$", ty := Ty.rfun, pred := isDistribution },
    { sing := phrase!"distribution $v$ on $\\mathbb{N}_0$",
      plural := phrase!"distributions $v$ on $\\mathbb{N}_0$", ty := Ty.rfun, pred := isDistribution }]
  notions := [
    { name := phrase!"Poisson distribution with mean $v$", value := poisson, ty := .real ⟶ Ty.rfun,
      doms := [dom (.le (.num 0) (.loc 0))] },
    { name := phrase!"binomial distribution with parameters $v$ and $v$", value := binomial,
      ty := .real ⟶ .real ⟶ Ty.rfun,
      doms := [dom (isNat (.loc 0)), dom (.and (.le (.num 0) (.loc 0)) (.le (.loc 0) (.num 1)))] },
    { name := phrase!"negative binomial distribution with parameters $v$ and $v$", value := negBinomial,
      ty := .real ⟶ .real ⟶ Ty.rfun,
      doms := [dom (.and (isNat (.loc 0)) (.le (.num 1) (.loc 0))),
        dom (.and (.lt (.num 0) (.loc 0)) (.le (.loc 0) (.num 1)))] },
    { name := phrase!"point mass at $v$", value := pointMass, ty := .real ⟶ Ty.rfun,
      doms := [dom (isNat (.loc 0))] },
    { name := phrase!"mean of $v$", value := mean, ty := Ty.rfun ⟶ .real, doms := [none] }]

/-- The core vocabulary followed by this one. -/
def withCore : Vocab := Vocab.core ++ vocab

end Leanify.Distributions
