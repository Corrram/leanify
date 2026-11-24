import Leanify.Library.Core

/-! # Vocabulary: probability densities on the line

A probability density is a real function `f ≥ 0` on the line, integrable, with
`∫_{-∞}^{∞} f = 1` (the density of an absolutely continuous distribution, with respect to
Lebesgue measure), so that an article binds densities by a noun (`Let $f$ be a probability
density.`) and writes `f(x)` and its integrals.

* nouns: `probability density`, `probability density function`;
* adjectives: `symmetric`, `symmetric about $\mu$`, `supported on $[a,b]$`, `with finite
  mean`, `with finite variance`, `with mean $\mu$`, `unimodal`, `log-concave`;
* the standard densities, with their parameters: normal (`with mean $\mu$ and variance
  $\sigma^2$`, and the standard normal density), exponential, uniform on `[a,b]`, gamma,
  beta, chi-squared, Cauchy, Laplace, logistic, Pareto and Weibull densities;
* notions of a density: its distribution function, mean (`the mean of the density $f$`),
  variance, `k`th moment, moment generating function, median and differential entropy.

The densities are terms of the core language (exponentials, powers, integrals over the
line); the gamma function, in the gamma, beta and chi-squared densities, is Mathlib's
`Real.Gamma`. A notion is defined where its integral is: the mean of a density with a
finite mean, the variance of one with a finite variance, the moment generating function at
the `t` where `e^{tx}f(x)` is integrable, the median if exactly one number has half of the
mass below it. -/

namespace Leanify.Densities
open Build Core

abbrev F : Ty := Ty.rfun

def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def rpow (x p : B) : B := app2 (prim .rpow) x p
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def pi : B := prim .pi
def gamma (x : B) : B := app (const 0) x
def sq (x : B) : B := mul x x

/-- The whole line, as a set. -/
def line : B := lamR fun _ => tt
/-- `∫_{-∞}^{∞} g`, and that `g` is integrable on the line. -/
def integral (g : B) : B := app2 (prim .integralOn) line g
def integrable (g : B) : B := app2 (prim .integrableOn) g line
/-- `∫_{-∞}^{x} g`. -/
def integralTo (x g : B) : B := app2 (prim .integralOn) (lamR fun t => le t x) g

/-- `x ↦ x^k f(x)`, for a natural number `k` (`zpow`). -/
def moment (k f : B) : B := lamR fun x => mul (app2 (prim .zpow) x k) (app f x)
def xf (f : B) : B := lamR fun x => mul x (app f x)
def x2f (f : B) : B := lamR fun x => mul (mul x x) (app f x)

/-- `f` is a probability density. -/
def isDensity (f : B) : B :=
  and (allR fun x => le (num 0) (app f x)) (and (integrable f) (eq (integral f) (num 1)))

def mean (f : B) : B := integral (xf f)
def finiteMean (f : B) : B := integrable (xf f)
def finiteVariance (f : B) : B := integrable (x2f f)

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p

def posP (x : B) : B := lt (num 0) x
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posIntP (n : B) : B := and (isInt n) (lt (num 0) n)
/-- There is exactly one `m` with `p m`. -/
def exUnique (p : B → B) : B := exR fun m => and (p m) (allR fun m' => imp (p m') (eq m' m))

/-- A real parameter, in its domain (`none`: every real number). -/
def par (d : Option (B → B)) (b : B → B) : B := match d with | some p => lamT .real p b | none => lamR b
def parDom (d : Option (B → B)) : Option Tm := d.bind (dom1 .real)

/-- A density with its parameters (each with its domain), `x ↦ body`. -/
def dens1 (name : Phrase) (d : Option (B → B)) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F, doms := [parDom d], doc, value := close <| par d fun a => lamR fun x => body a x }
def dens2 (name : Phrase) (d1 d2 : Option (B → B)) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ F, doms := [parDom d1, parDom d2], doc,
    value := close <| par d1 fun a => par d2 fun b => lamR fun x => body a b x }

def normal (m v x : B) : B := div (exp (neg (div (sq (sub x m)) (mul (num 2) v)))) (sqrt (mul (mul (num 2) pi) v))
/-- The gamma density with shape `k` and rate `β`. -/
def gammaD (k r x : B) : B :=
  cases (lt (num 0) x) (div (mul (mul (rpow r k) (rpow x (sub k (num 1)))) (exp (neg (mul r x)))) (gamma k)) (num 0)

/-- A notion of a density with the condition `c` (a finite mean, …), in its domain. -/
def ofD (name : Phrase) (ty : Ty) (body : B → B) (c : Option (B → B)) (doc : String) : Notion :=
  let d := fun f => match c with | some c => and (isDensity f) (c f) | none => isDensity f
  { name, ty := F ⟶ ty, doms := [dom1 F d], doc, value := close <| lamT F d body }

/-- The uniform density on `[a,b]`, `a < b`. -/
def uniformD (name : Phrase) : Notion :=
  { name, ty := .real ⟶ .real ⟶ F, doc := "`1/(b - a)` on `[a,b]`, `0` else; `a < b`",
    doms := [none, dom2 .real fun a b => lt a b],
    value := close <| lamR fun a => lamT .real (fun b => lt a b) fun b =>
      lamR fun x => cases (and (le a x) (le x b)) (div (num 1) (sub b a)) (num 0) }

def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred, doc }

def vocab : Vocab where
  consts := [.real ⟶ .real]
  constNames := [w!"\\Gamma"]
  constLean := [w!"Real.Gamma"]
  modules := [w!"Mathlib.Analysis.SpecialFunctions.Gamma.Basic"]
  nouns := [
    { sing := phrase!"probability density", plural := phrase!"probability densities", ty := F,
      pred := fPred isDensity,
      doc := "`f ≥ 0`, integrable, `∫ f = 1` (Mathlib `MeasureTheory.pdf`)" },
    { sing := phrase!"probability density function", plural := phrase!"probability density functions", ty := F,
      pred := fPred isDensity, doc := "a probability density" }]
  mods := [
    mod phrase!"symmetric" true (fPred fun f => allR fun x => eq (app f (neg x)) (app f x)) "`f(-x) = f(x)`",
    mod phrase!"symmetric about $v$" false
      (close <| lamR fun m => lamT F (fun _ => tt) fun f => allR fun x => eq (app f (sub m x)) (app f (add m x)))
      "`f(μ - x) = f(μ + x)`",
    mod phrase!"supported on $[v,v]$" false
      (close <| lamR fun a => lamR fun b => lamT F (fun _ => tt) fun f =>
        allR fun x => imp (or (lt x a) (lt b x)) (eq (app f x) (num 0)))
      "`f(x) = 0` outside `[a,b]`",
    mod phrase!"with finite mean" false (fPred finiteMean) "`x f(x)` is integrable",
    mod phrase!"with finite variance" false (fPred finiteVariance) "`x² f(x)` is integrable",
    mod phrase!"with mean $v$" false
      (close <| lamR fun m => lamT F (fun _ => tt) fun f => and (finiteMean f) (eq (mean f) m))
      "`∫ x f(x) dx = μ`",
    mod phrase!"unimodal" true
      (fPred fun f => exR fun m => and (allR fun x => allR fun y => imp (and (le x y) (le y m)) (le (app f x) (app f y)))
        (allR fun x => allR fun y => imp (and (le m x) (le x y)) (le (app f y) (app f x))))
      "nondecreasing up to a mode `m`, nonincreasing after it",
    mod phrase!"log-concave" true
      (fPred fun f => allR fun x => allR fun y => allR fun t => imp (and (le (num 0) t) (le t (num 1)))
        (le (mul (rpow (app f x) t) (rpow (app f y) (sub (num 1) t))) (app f (add (mul t x) (mul (sub (num 1) t) y)))))
      "`f(tx + (1-t)y) ≥ f(x)^t f(y)^{1-t}`"]
  notions := [
    dens2 phrase!"normal density with mean $v$ and variance $v$" none (some posP) normal
      "`e^{-(x-μ)²/(2σ²)}/√(2πσ²)`, `σ² > 0` (Mathlib `ProbabilityTheory.gaussianPDFReal`)",
    dens2 phrase!"density of the normal distribution with mean $v$ and variance $v$" none (some posP) normal
      "`e^{-(x-μ)²/(2σ²)}/√(2πσ²)`, `σ² > 0`",
    { name := phrase!"standard normal density", ty := F, doc := "`e^{-x²/2}/√(2π)`",
      value := close <| lamR fun x => normal (num 0) (num 1) x },
    dens1 phrase!"density of the exponential distribution with rate $v$" (some posP)
      (fun r x => cases (le (num 0) x) (mul r (exp (neg (mul r x)))) (num 0))
      "`λ e^{-λx}` for `x ≥ 0`, `0` else; `λ > 0` (Mathlib `ProbabilityTheory.exponentialPDFReal`)",
    dens1 phrase!"exponential density with rate $v$" (some posP)
      (fun r x => cases (le (num 0) x) (mul r (exp (neg (mul r x)))) (num 0)) "`λ e^{-λx}` for `x ≥ 0`",
    uniformD phrase!"density of the uniform distribution on $[v,v]$",
    uniformD phrase!"uniform density on $[v,v]$",
    dens2 phrase!"density of the gamma distribution with shape $v$ and rate $v$" (some posP) (some posP) gammaD
      "`β^k x^{k-1} e^{-βx}/Γ(k)` for `x > 0`; `k, β > 0` (Mathlib `ProbabilityTheory.gammaPDFReal`)",
    dens2 phrase!"density of the beta distribution with parameters $v$ and $v$" (some posP) (some posP)
      (fun a b x => cases (and (lt (num 0) x) (lt x (num 1)))
        (div (mul (mul (rpow x (sub a (num 1))) (rpow (sub (num 1) x) (sub b (num 1)))) (gamma (add a b)))
          (mul (gamma a) (gamma b))) (num 0))
      "`x^{a-1}(1-x)^{b-1} Γ(a+b)/(Γ(a)Γ(b))` on `(0,1)`; `a, b > 0`",
    dens1 phrase!"density of the chi-squared distribution with $v$ degrees of freedom" (some posIntP)
      (fun k x => gammaD (div k (num 2)) (div (num 1) (num 2)) x)
      "the gamma density with shape `k/2` and rate `1/2`, `k` a positive integer",
    dens2 phrase!"density of the Cauchy distribution with location $v$ and scale $v$" none (some posP)
      (fun m s x => div (num 1) (mul (mul pi s) (add (num 1) (sq (div (sub x m) s)))))
      "`1/(πγ(1 + ((x-x₀)/γ)²))`, `γ > 0`",
    { name := phrase!"standard Cauchy density", ty := F, doc := "`1/(π(1 + x²))`",
      value := close <| lamR fun x => div (num 1) (mul pi (add (num 1) (sq x))) },
    dens2 phrase!"density of the Laplace distribution with location $v$ and scale $v$" none (some posP)
      (fun m b x => div (exp (neg (div (abs (sub x m)) b))) (mul (num 2) b)) "`e^{-|x-μ|/b}/(2b)`, `b > 0`",
    dens2 phrase!"density of the logistic distribution with location $v$ and scale $v$" none (some posP)
      (fun m s x => div (exp (neg (div (sub x m) s))) (mul s (sq (add (num 1) (exp (neg (div (sub x m) s)))))))
      "`e^{-(x-μ)/s}/(s(1 + e^{-(x-μ)/s})²)`, `s > 0`",
    dens2 phrase!"density of the Pareto distribution with scale $v$ and shape $v$" (some posP) (some posP)
      (fun m a x => cases (le m x) (div (mul a (rpow m a)) (rpow x (add a (num 1)))) (num 0))
      "`α x_m^α / x^{α+1}` for `x ≥ x_m`; `x_m, α > 0`",
    dens2 phrase!"density of the Weibull distribution with shape $v$ and scale $v$" (some posP) (some posP)
      (fun k l x => cases (lt (num 0) x)
        (mul (mul (div k l) (rpow (div x l) (sub k (num 1)))) (exp (neg (rpow (div x l) k)))) (num 0))
      "`(k/λ)(x/λ)^{k-1} e^{-(x/λ)^k}` for `x > 0`; `k, λ > 0`",
    ofD phrase!"distribution function of $v$" F (fun f => lamR fun x => integralTo x f) none
      "`x ↦ ∫_{-∞}^{x} f`",
    -- (`mean of $v$` alone is the mean of a distribution on `ℕ₀`, in the field `distributions`:
    -- the two fields are read together in the bundle `probability`)
    ofD phrase!"mean of the density $v$" .real mean (some finiteMean) "`∫ x f(x) dx`, of a density with a finite mean",
    ofD phrase!"variance of $v$" .real (fun f => sub (integral (x2f f)) (mul (mean f) (mean f))) (some finiteVariance)
      "`∫ x² f(x) dx - (∫ x f(x) dx)²`, of a density with a finite variance",
    ofD phrase!"variance of the density $v$" .real (fun f => sub (integral (x2f f)) (mul (mean f) (mean f))) (some finiteVariance)
      "`∫ x² f(x) dx - (∫ x f(x) dx)²`, of a density with a finite variance",
    { name := phrase!"$v$th moment of $v$", ty := .real ⟶ F ⟶ .real,
      doms := [dom1 .real natP, dom2 F fun k f => and (isDensity f) (integrable (moment k f))],
      doc := "`∫ x^k f(x) dx`, where `x^k f(x)` is integrable",
      value := close <| lamT .real natP fun k => lamT F (fun f => and (isDensity f) (integrable (moment k f)))
        fun f => integral (moment k f) },
    { name := phrase!"moment generating function of $v$", ty := F ⟶ F,
      doms := [dom1 F isDensity, dom2 .real fun f t => integrable (lamR fun x => mul (exp (mul t x)) (app f x))],
      doc := "`t ↦ ∫ e^{tx} f(x) dx`, at the `t` where `e^{tx} f(x)` is integrable",
      value := close <| lamT F isDensity fun f =>
        lamT .real (fun t => integrable (lamR fun x => mul (exp (mul t x)) (app f x)))
          fun t => integral (lamR fun x => mul (exp (mul t x)) (app f x)) },
    ofD phrase!"median of $v$" .real
      (fun f => theR fun m => eq (integralTo m f) (div (num 1) (num 2)))
      (some fun f => exUnique fun m => eq (integralTo m f) (div (num 1) (num 2)))
      "the `m` with `∫_{-∞}^{m} f = 1/2`, if there is exactly one",
    ofD phrase!"median of the density $v$" .real
      (fun f => theR fun m => eq (integralTo m f) (div (num 1) (num 2)))
      (some fun f => exUnique fun m => eq (integralTo m f) (div (num 1) (num 2)))
      "the `m` with `∫_{-∞}^{m} f = 1/2`, if there is exactly one",
    ofD phrase!"differential entropy of $v$" .real
      (fun f => neg (integral (lamR fun x => cases (eq (app f x) (num 0)) (num 0) (mul (app f x) (log (app f x))))))
      (some fun f => integrable (lamR fun x => cases (eq (app f x) (num 0)) (num 0) (mul (app f x) (log (app f x)))))
      "`-∫ f log f` (`0 log 0 = 0`), where `f log f` is integrable"]

end Leanify.Densities
