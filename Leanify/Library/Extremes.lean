import Leanify.Library.Core

/-! # Vocabulary: extreme value theory

The generalized extreme value and generalized Pareto distribution functions, return
levels, and the maximum domains of attraction of a distribution function `F` (a
nondecreasing real function): `$F$ is in the maximum domain of attraction of the Gumbel
distribution`.

* notions: the GEV distribution function with shape `ξ`, location `μ` and scale `σ > 0`
  (`exp(-(1 + ξ(x-μ)/σ)^{-1/ξ})` where `1 + ξ(x-μ)/σ > 0`, `exp(-e^{-(x-μ)/σ})` for `ξ = 0`,
  and `0` or `1` outside the support), the standard Gumbel, Fréchet (`α > 0`) and reversed
  Weibull distribution functions, the return level for the return period `T > 1`
  (`μ - (σ/ξ)(1 - (-log(1 - 1/T))^{-ξ})`, `μ - σ log(-log(1 - 1/T))` for `ξ = 0`), the
  generalized Pareto distribution function with shape `ξ` and scale `σ` (`1 - (1 + ξx/σ)^{-1/ξ}`),
  the mean excess `σ/(1-ξ)` of the generalized Pareto distribution for `ξ < 1`;
* adjectives of distribution functions: `in the maximum domain of attraction of the Gumbel
  distribution` (`F(a_n x + b_n)^n → e^{-e^{-x}}` for some `a_n > 0`, `b_n`), `… of the Fréchet
  distribution with index $\alpha$`, `… of the Weibull distribution with index $\alpha$`,
  `regularly varying in the tail with index $\alpha$` (`(1 - F(tx))/(1 - F(t)) → x^{-α}`).

Every meaning is a term of the core language. -/

namespace Leanify.Extremes
open Build Core

abbrev F : Ty := Ty.rfun

def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def rpow (x y : B) : B := app2 (prim .rpow) x y
def pos (x : B) : B := lt (num 0) x
def zpow (x k : B) : B := app2 (prim .zpow) x k
def nat (n : B) : B := and (isInt n) (le (num 1) n)
def gev (xi mu s x : B) : B :=
  cases (eq xi (num 0)) (exp (neg (exp (neg (div (sub x mu) s)))))
    (cases (lt (num 0) (add (num 1) (mul xi (div (sub x mu) s))))
      (exp (neg (rpow (add (num 1) (mul xi (div (sub x mu) s))) (neg (div (num 1) xi)))))
      (cases (lt (num 0) xi) (num 0) (num 1)))
def gumbel (x : B) : B := exp (neg (exp (neg x)))
def frechet (a x : B) : B := cases (lt (num 0) x) (exp (neg (rpow x (neg a)))) (num 0)
def weibull (a x : B) : B := cases (lt x (num 0)) (exp (neg (rpow (neg x) a))) (num 1)
/-- `F(a_n x + b_n)^n → G(x)` for every `x`, for some norming sequences. -/
def attracted (f : B) (g : B → B) : B :=
  exT F fun a => exT F fun b => and (allR fun n => imp (nat n) (pos (app a n)))
    (allR fun x => allR fun e => imp (pos e) (exR fun n0 => allR fun n => imp (and (nat n) (le n0 n))
      (lt (abs (sub (zpow (app f (add (mul (app a n) x) (app b n))) n) (g x))) e)))
def tailRatio (f t x : B) : B := div (sub (num 1) (app f (mul t x))) (sub (num 1) (app f t))
def rv (f a : B) : B :=
  and (allR fun t => lt (app f t) (num 1))
    (allR fun x => imp (pos x) (allR fun e => imp (pos e) (exR fun t0 => allR fun t => imp (le t0 t)
      (lt (abs (sub (tailRatio f t x) (rpow x (neg a)))) e))))
def any (_ : B) : B := tt
def fdist (p : Phrase) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, pred := close <| lamT F any body, doc }
def fdistA (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, pred := close <| lamT .real pos fun a => lamT F any fun f => body a f, doc }
def returnLevel (xi mu s t : B) : B :=
  cases (eq xi (num 0)) (sub mu (mul s (log (neg (log (sub (num 1) (div (num 1) t)))))))
    (sub mu (mul (div s xi) (sub (num 1) (rpow (neg (log (sub (num 1) (div (num 1) t)))) (neg xi)))))

def vocab : Vocab where
  mods := [
    fdist phrase!"in the maximum domain of attraction of the Gumbel distribution" (fun f => attracted f gumbel)
      "`F(a_n x + b_n)^n → exp(-e^{-x})` for some `a_n > 0`, `b_n`",
    fdistA phrase!"in the maximum domain of attraction of the Fréchet distribution with index $v$"
      (fun a f => attracted f (frechet a)) "`F(a_n x + b_n)^n → Φ_α(x)`",
    fdistA phrase!"in the maximum domain of attraction of the Frechet distribution with index $v$"
      (fun a f => attracted f (frechet a)) "the Fréchet case",
    fdistA phrase!"in the maximum domain of attraction of the Weibull distribution with index $v$"
      (fun a f => attracted f (weibull a)) "`F(a_n x + b_n)^n → Ψ_α(x)`",
    fdistA phrase!"regularly varying in the tail with index $v$" (fun a f => rv f a)
      "`F(t) < 1` and `(1 - F(tx))/(1 - F(t)) → x^{-α}` as `t → ∞`, for `x > 0`"]
  notions := [
    { name := phrase!"generalized extreme value distribution function with shape $v$, location $v$ and scale $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ F, doms := [none, none, dom1 .real pos],
      doc := "`exp(-(1 + ξ(x-μ)/σ)^{-1/ξ})` on the support, `exp(-e^{-(x-μ)/σ})` for `ξ = 0`",
      value := close <| lamR fun xi => lamR fun mu => lamT .real pos fun s => lamR fun x => gev xi mu s x },
    { name := phrase!"standard Gumbel distribution function", ty := F, doc := "`exp(-e^{-x})`",
      value := close <| lamR fun x => gumbel x },
    { name := phrase!"Fréchet distribution function with index $v$", ty := .real ⟶ F, doms := [dom1 .real pos],
      doc := "`exp(-x^{-α})` for `x > 0`, `0` otherwise",
      value := close <| lamT .real pos fun a => lamR fun x => frechet a x },
    { name := phrase!"Frechet distribution function with index $v$", ty := .real ⟶ F, doms := [dom1 .real pos],
      doc := "the Fréchet distribution function",
      value := close <| lamT .real pos fun a => lamR fun x => frechet a x },
    { name := phrase!"reversed Weibull distribution function with index $v$", ty := .real ⟶ F, doms := [dom1 .real pos],
      doc := "`exp(-(-x)^α)` for `x < 0`, `1` otherwise",
      value := close <| lamT .real pos fun a => lamR fun x => weibull a x },
    { name := phrase!"return level for the return period $v$ with shape $v$, location $v$ and scale $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real fun t => lt (num 1) t, none, none, dom1 .real pos],
      doc := "the `(1 - 1/T)`-quantile of the GEV distribution",
      value := close <| lamT .real (fun t => lt (num 1) t) fun t => lamR fun xi => lamR fun mu => lamT .real pos fun s =>
        returnLevel xi mu s t },
    { name := phrase!"generalized Pareto distribution function with shape $v$ and scale $v$", ty := .real ⟶ .real ⟶ F,
      doms := [none, dom1 .real pos],
      doc := "`1 - (1 + ξx/σ)^{-1/ξ}` for `x ≥ 0` on the support, `1 - e^{-x/σ}` for `ξ = 0`",
      value := close <| lamR fun xi => lamT .real pos fun s => lamR fun x =>
        cases (lt x (num 0)) (num 0)
          (cases (eq xi (num 0)) (sub (num 1) (exp (neg (div x s))))
            (cases (lt (num 0) (add (num 1) (mul xi (div x s)))) (sub (num 1) (rpow (add (num 1) (mul xi (div x s))) (neg (div (num 1) xi)))) (num 1))) },
    { name := phrase!"mean excess of the generalized Pareto distribution with shape $v$ and scale $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun xi => lt xi (num 1), dom1 .real pos], doc := "`σ/(1 - ξ)` at `0`, for `ξ < 1`",
      value := close <| lamT .real (fun xi => lt xi (num 1)) fun xi => lamT .real pos fun s => div s (sub (num 1) xi) }]

end Leanify.Extremes
