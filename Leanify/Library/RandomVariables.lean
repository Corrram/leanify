import Leanify.Library.Core
import Leanify.Library.Densities

/-! # Vocabulary: real random variables

A random variable is a real function of the outcome `ω` of one probability space for the
whole article, `[0,1]` with Lebesgue measure (`Leanify/Library/RandomVariablesModel.lean`
says why this loses nothing): an article binds random variables by a noun (`Let $X$ and
$Y$ be independent random variables.`) and writes

* `\mathbb{E}[e]`, `\mathbb{E}(e)`, `E[e]`, `\mathbb{E}X` for the expectation of an
  expression `e` in the random variables (`\mathbb{E}[X^2]`, `\mathbb{E}[XY]`,
  `\mathbb{E}[\frac1n\sum_{i=1}^n X_i]`), defined where `e` is integrable;
* `P(φ)`, `\mathbb{P}(φ)`, `\Pr(φ)` for the probability of a condition on them
  (`P(X\ge a)`, `P(|X-\mu|\ge k\sigma)`) or of an event (`P(A\cap B)`), and `P(A\mid B)`,
  defined where `P(B)>0`;
* `\operatorname{Var}(e)` and `\operatorname{Cov}(e,f)`, defined where the expressions are
  square-integrable.

* nouns: `random variable`, `real random variable`, `real-valued random variable`, `event`;
* adjectives: `nonnegative`, `positive`, `integrable`, `square-integrable`, `bounded`,
  `with finite mean`, `with finite variance`, `with mean $\mu$`, `with variance $\sigma^2$`,
  `with mean $\mu$ and variance $\sigma^2$`; the distributions `standard normal`,
  `normal` (`normally distributed with mean $\mu$ and variance $\sigma^2$`), `exponential`
  (`with rate $\lambda$`), `uniform` (`on $[a,b]$`), `Poisson` (`with parameter
  $\lambda$`), `Bernoulli` (`with parameter $p$`), `binomial` (`with parameters $n$ and
  $p$`), each by its distribution function or its probabilities;
* collective adjectives (`independent random variables $X$ and $Y$`, `$X_1,\ldots,X_n$
  are independent and identically distributed`): independence by the factorization of
  the joint distribution function, identical distribution by the distribution functions;
* notions: the expectation (expected value) and standard deviation of a random variable,
  the probability of an event (the variance is `\operatorname{Var}(X)`). -/

namespace Leanify.RandomVariables
open Build Core

/-- Random variables: the field's base type. -/
abbrev R : Ty := .base 0

/-- `X(ω)`. -/
def ev (x w : B) : B := app2 (const 0) x w
/-- The outcomes: `[0,1]`. -/
def inOmega (w : B) : B := and (le (num 0) w) (le w (num 1))
/-- The probability of the outcomes with `s ω`. -/
def probSet (s : B → B) : B :=
  app2 (prim .integralOn) (lamR fun w => and (inOmega w) (s w)) (lamR fun _ => num 1)
/-- `ω ↦ f ω` is integrable, and its expectation. -/
def integ (f : B → B) : B := app2 (prim .integrableOn) (lamR f) (lamR inOmega)
def expect (f : B → B) : B := app2 (prim .integralOn) (lamR inOmega) (lamR f)
/-- `P(X ≤ t)`. -/
def cdf (x t : B) : B := probSet fun w => le (ev x w) t
def sq (x : B) : B := mul x x
def meanOf (x : B) : B := expect fun w => ev x w
def varOf (x : B) : B := sub (expect fun w => sq (ev x w)) (sq (meanOf x))

def rvPred (p : B → B) : Tm := close <| lamT R (fun _ => tt) p
/-- A modifier of random variables. -/
def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := R, pred, doc }
def mod1 (p : Phrase) (q : B → B → B) (doc : String) : Modifier :=
  mod p false (close <| lamR fun a => lamT R (fun _ => tt) fun x => q a x) doc
def mod2 (p : Phrase) (q : B → B → B → B) (doc : String) : Modifier :=
  mod p false (close <| lamR fun a => lamR fun b => lamT R (fun _ => tt) fun x => q a b x) doc

/-! ## Distributions, by their distribution functions or probabilities -/

def zpow (x k : B) : B := app2 (prim .zpow) x k
def factorial (k : B) : B := app (prim .factorial) k
def binom (n k : B) : B := app2 (prim .binom) n k

def normalLaw (m v x : B) : B :=
  and (lt (num 0) v) (allR fun t => eq (cdf x t) (Densities.integralTo t (lamR fun y => Densities.normal m v y)))
def expLaw (l x : B) : B :=
  and (lt (num 0) l) (and (eq (probSet fun w => lt (ev x w) (num 0)) (num 0))
    (allR fun t => imp (le (num 0) t) (eq (cdf x t) (sub (num 1) (Densities.exp (neg (mul l t)))))))
def uniformLaw (a b x : B) : B :=
  and (lt a b) (and (eq (probSet fun w => and (le a (ev x w)) (le (ev x w) b)) (num 1))
    (allR fun t => imp (and (le a t) (le t b)) (eq (cdf x t) (div (sub t a) (sub b a)))))
def poissonLaw (l x : B) : B :=
  and (lt (num 0) l) (allR fun k => imp (isNat k)
    (eq (probSet fun w => eq (ev x w) k) (div (mul (Densities.exp (neg l)) (zpow l k)) (factorial k))))
def bernoulliLaw (p x : B) : B :=
  and (and (le (num 0) p) (le p (num 1)))
    (and (eq (probSet fun w => eq (ev x w) (num 1)) p) (eq (probSet fun w => eq (ev x w) (num 0)) (sub (num 1) p)))
def binomialLaw (n p x : B) : B :=
  and (and (isNat n) (and (le (num 0) p) (le p (num 1))))
    (allR fun k => imp (and (isNat k) (le k n))
      (eq (probSet fun w => eq (ev x w) k) (mul (binom n k) (mul (zpow p k) (zpow (sub (num 1) p) (sub n k))))))

def vocab : Vocab where
  types := [w!"\\mathrm{RV}"]
  consts := [R ⟶ .real ⟶ .real, R ⟶ .prop]
  constNames := [w!"#1(#2)", w!"\\operatorname{RV}"]
  constLean := [w!"Leanify.RandomVariables.eval", w!"Leanify.RandomVariables.IsRV"]
  typeLean := [(w!"Leanify.RandomVariables.RV", w!"Leanify.RandomVariables.RV.zero")]
  modules := [w!"Leanify.Library.RandomVariablesModel"]
  nouns := [
    { sing := phrase!"random variable", plural := phrase!"random variables", ty := R, pred := .const 1,
      doc := "a measurable function of the outcome (Mathlib `Measurable`), on `[0,1]` with Lebesgue measure" },
    { sing := phrase!"real random variable", plural := phrase!"real random variables", ty := R, pred := .const 1,
      doc := "(Mathlib `Measurable`)" },
    { sing := phrase!"real-valued random variable", plural := phrase!"real-valued random variables", ty := R, pred := .const 1,
      doc := "(Mathlib `Measurable`)" },
    { sing := phrase!"event", plural := phrase!"events", ty := .real ⟶ .prop, pred := close (lamT (.real ⟶ .prop) (fun _ => tt) fun _ => tt),
      doc := "a set of outcomes, whose probability is `P(A)`" }]
  mods := [
    mod phrase!"nonnegative" true (rvPred fun x => eq (probSet fun w => le (num 0) (ev x w)) (num 1)) "`X ≥ 0` almost surely",
    mod phrase!"non-negative" true (rvPred fun x => eq (probSet fun w => le (num 0) (ev x w)) (num 1)) "`X ≥ 0` almost surely",
    mod phrase!"positive" true (rvPred fun x => eq (probSet fun w => lt (num 0) (ev x w)) (num 1)) "`X > 0` almost surely",
    mod phrase!"integrable" true (rvPred fun x => integ fun w => ev x w) "`𝔼|X| < ∞` (Mathlib `Integrable`)",
    mod phrase!"square-integrable" true (rvPred fun x => integ fun w => sq (ev x w)) "`𝔼[X²] < ∞` (Mathlib `MemLp X 2`)",
    mod phrase!"bounded" true (rvPred fun x => exR fun c => eq (probSet fun w => le (abs (ev x w)) c) (num 1))
      "`|X| ≤ c` almost surely, for some `c`",
    mod phrase!"normally distributed" true (rvPred fun x => exR fun m => exR fun v => normalLaw m v x) "with a normal distribution",
    mod phrase!"exponentially distributed" true (rvPred fun x => exR fun l => expLaw l x) "with an exponential distribution",
    mod phrase!"Poisson distributed" true (rvPred fun x => exR fun l => poissonLaw l x) "with a Poisson distribution",
    mod phrase!"uniformly distributed" true (rvPred fun x => exR fun a => exR fun b => uniformLaw a b x) "uniform on some `[a,b]`",
    mod phrase!"standard normal" true (rvPred fun x => normalLaw (num 0) (num 1) x) "with the distribution `N(0,1)`",
    mod phrase!"normal" true (rvPred fun x => exR fun m => exR fun v => normalLaw m v x) "with a normal distribution `N(μ,σ²)`, `σ² > 0`",
    mod phrase!"Gaussian" true (rvPred fun x => exR fun m => exR fun v => normalLaw m v x) "with a normal distribution",
    mod phrase!"exponential" true (rvPred fun x => exR fun l => expLaw l x) "with an exponential distribution",
    mod phrase!"Poisson" true (rvPred fun x => exR fun l => poissonLaw l x) "with a Poisson distribution",
    mod phrase!"Bernoulli" true (rvPred fun x => exR fun p => bernoulliLaw p x) "with values `0` and `1`",
    mod phrase!"binomial" true (rvPred fun x => exR fun n => exR fun p => binomialLaw n p x) "with a binomial distribution",
    mod phrase!"with finite mean" false (rvPred fun x => integ fun w => ev x w) "`𝔼|X| < ∞`",
    mod phrase!"with finite expectation" false (rvPred fun x => integ fun w => ev x w) "`𝔼|X| < ∞`",
    mod phrase!"with finite variance" false (rvPred fun x => integ fun w => sq (ev x w)) "`𝔼[X²] < ∞`",
    mod phrase!"with finite second moment" false (rvPred fun x => integ fun w => sq (ev x w)) "`𝔼[X²] < ∞`",
    mod phrase!"with mean zero" false (rvPred fun x => and (integ fun w => ev x w) (eq (meanOf x) (num 0))) "`𝔼X = 0`",
    mod phrase!"with zero mean" false (rvPred fun x => and (integ fun w => ev x w) (eq (meanOf x) (num 0))) "`𝔼X = 0`",
    mod1 phrase!"with mean $v$" (fun m x => and (integ fun w => ev x w) (eq (meanOf x) m)) "`𝔼X = μ`",
    mod1 phrase!"with expectation $v$" (fun m x => and (integ fun w => ev x w) (eq (meanOf x) m)) "`𝔼X = μ`",
    mod1 phrase!"with expected value $v$" (fun m x => and (integ fun w => ev x w) (eq (meanOf x) m)) "`𝔼X = μ`",
    mod1 phrase!"with variance $v$" (fun v x => and (integ fun w => sq (ev x w)) (eq (varOf x) v)) "`Var X = σ²`",
    mod1 phrase!"with finite variance $v$" (fun v x => and (integ fun w => sq (ev x w)) (eq (varOf x) v)) "`Var X = σ² < ∞`",
    mod1 phrase!"with finite mean $v$" (fun m x => and (integ fun w => ev x w) (eq (meanOf x) m)) "`𝔼X = μ`",
    mod2 phrase!"with mean $v$ and variance $v$" (fun m v x =>
      and (integ fun w => sq (ev x w)) (and (eq (meanOf x) m) (eq (varOf x) v))) "`𝔼X = μ`, `Var X = σ²`",
    mod2 phrase!"normally distributed with mean $v$ and variance $v$" normalLaw "`N(μ,σ²)`, `σ² > 0`",
    mod2 phrase!"with a normal distribution with mean $v$ and variance $v$" normalLaw "`N(μ,σ²)`",
    mod2 phrase!"with the normal distribution with mean $v$ and variance $v$" normalLaw "`N(μ,σ²)`",
    mod phrase!"standard normally distributed" false (rvPred fun x => normalLaw (num 0) (num 1) x) "`N(0,1)`",
    mod phrase!"with a standard normal distribution" false (rvPred fun x => normalLaw (num 0) (num 1) x) "`N(0,1)`",
    mod phrase!"with the standard normal distribution" false (rvPred fun x => normalLaw (num 0) (num 1) x) "`N(0,1)`",
    mod1 phrase!"exponentially distributed with rate $v$" expLaw "`P(X ≤ t) = 1 - e^{-λt}`, `t ≥ 0`",
    mod1 phrase!"exponentially distributed with parameter $v$" expLaw "the rate `λ`",
    mod1 phrase!"with an exponential distribution with rate $v$" expLaw "`P(X ≤ t) = 1 - e^{-λt}`",
    mod1 phrase!"with an exponential distribution with parameter $v$" expLaw "the rate `λ`",
    mod2 phrase!"uniformly distributed on $[v,v]$" uniformLaw "`P(X ≤ t) = (t-a)/(b-a)` on `[a,b]`",
    mod2 phrase!"with a uniform distribution on $[v,v]$" uniformLaw "on `[a,b]`",
    mod2 phrase!"with the uniform distribution on $[v,v]$" uniformLaw "on `[a,b]`",
    mod1 phrase!"Poisson distributed with parameter $v$" poissonLaw "`P(X = k) = e^{-λ}λ^k/k!`",
    mod1 phrase!"Poisson distributed with mean $v$" poissonLaw "`P(X = k) = e^{-λ}λ^k/k!`",
    mod1 phrase!"with a Poisson distribution with parameter $v$" poissonLaw "`P(X = k) = e^{-λ}λ^k/k!`",
    mod1 phrase!"with a Poisson distribution with mean $v$" poissonLaw "`P(X = k) = e^{-λ}λ^k/k!`",
    mod1 phrase!"Bernoulli distributed with parameter $v$" bernoulliLaw "`P(X = 1) = p`, `P(X = 0) = 1-p`",
    mod1 phrase!"with a Bernoulli distribution with parameter $v$" bernoulliLaw "`P(X = 1) = p`, `P(X = 0) = 1-p`",
    mod2 phrase!"binomially distributed with parameters $v$ and $v$" binomialLaw "`P(X = k) = C(n,k)pᵏ(1-p)ⁿ⁻ᵏ`",
    mod2 phrase!"with a binomial distribution with parameters $v$ and $v$" binomialLaw "`P(X = k) = C(n,k)pᵏ(1-p)ⁿ⁻ᵏ`"]
  notions := [
    { name := phrase!"expectation of $v$", ty := R ⟶ .real, doc := "`𝔼X`, for an integrable `X`",
      value := close <| lamT R (fun _ => tt) fun x => guard (integ fun w => ev x w) (meanOf x) },
    { name := phrase!"expected value of $v$", ty := R ⟶ .real, doc := "`𝔼X`",
      value := close <| lamT R (fun _ => tt) fun x => guard (integ fun w => ev x w) (meanOf x) },
    { name := phrase!"standard deviation of $v$", ty := R ⟶ .real, doc := "`√Var X`",
      value := close <| lamT R (fun _ => tt) fun x => guard (integ fun w => sq (ev x w)) (Densities.sqrt (varOf x)) },
    { name := phrase!"probability of $v$", ty := (.real ⟶ .prop) ⟶ .real, doc := "`P(A)`",
      value := close <| lamT (.real ⟶ .prop) (fun _ => tt) fun a => probSet fun w => app a w }]
  methods := [
    { ty := R, op := .fn w!"@at", const := 0, doc := "the value at an outcome, inside `\\mathbb{E}[…]` and `P(…)`" }]

end Leanify.RandomVariables
