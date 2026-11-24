import Leanify.Library.Densities

/-! # Vocabulary: risk measures and reliability of densities

The quantities of actuarial science, risk management and reliability theory for a
distribution with a density on the line, the probability densities of the field
`densities` (`Let $f$ be a probability density.`).

* notions of a density: the survival function `S(x) = ∫_x^∞ f`, the hazard rate (also
  `hazard function` and `failure rate`) `f(x)/S(x)`, the cumulative hazard function
  `-log S(x)` (where `S(x) > 0`), the quantile function `u ↦ inf {x : F(x) ≥ u}` (for
  `0 < u < 1`), the stop-loss transform `d ↦ ∫_d^∞ (x-d) f(x) dx` and the mean excess
  function `u ↦ ∫_u^∞ (x-u) f(x) dx / S(u)` (of a density with a finite mean);
* risk measures at a level `0 < α < 1`: the value at risk, the expected shortfall (also
  `tail value at risk` and `conditional value at risk`), `(1/(1-α)) ∫_{VaR_α}^∞ x f(x) dx`;
* adjectives: `heavy-tailed` (`∫_0^∞ e^{tx} f(x) dx = ∞` for every `t > 0`),
  `light-tailed`, `with increasing failure rate`, `with decreasing failure rate`.

A quantile is a description: the least `x` with `F(x) ≥ u`, defined where exactly one
number is that least `x` (for a density, at every `0 < u < 1`). A monotone failure rate is
written without quotients, `f(x) S(y) ≤ f(y) S(x)` for `x ≤ y`, so that it is meaningful
where `S` vanishes. Every meaning is a term of the core language. -/

namespace Leanify.Risk
open Build Core
open Leanify.Densities (isDensity finiteMean integrable integralTo xf exUnique fPred)

abbrev F : Ty := Ty.rfun

def log (x : B) : B := app (prim (.realFn .log)) x
/-- `∫_{x}^{∞} g`. -/
def integralFrom (x g : B) : B := app2 (prim .integralOn) (lamR fun t => le x t) g
def integrableFrom (x g : B) : B := app2 (prim .integrableOn) g (lamR fun t => le x t)
/-- The survival function at `x`. -/
def surv (f x : B) : B := integralFrom x f
def cdf (f x : B) : B := integralTo x f
/-- `q` is the least `x` with `F(x) ≥ u`. -/
def isQuantile (f u q : B) : B := and (le u (cdf f q)) (allR fun x => imp (le u (cdf f x)) (le q x))
def level (u : B) : B := and (lt (num 0) u) (lt u (num 1))
def quantileDom (f u : B) : B := and (level u) (exUnique fun q => isQuantile f u q)
def quantile (f u : B) : B := theR fun q => isQuantile f u q
/-- `∫_d^∞ (x-d) f(x) dx`. -/
def stopLoss (f d : B) : B := integralFrom d (lamR fun x => mul (sub x d) (app f x))
def expShortfall (f a : B) : B := div (integralFrom (quantile f a) (xf f)) (sub (num 1) a)
def mgfTail (f t : B) : B := integrableFrom (num 0) (lamR fun x => mul (app (prim (.realFn .exp)) (mul t x)) (app f x))
/-- `f(x) S(y) ≤ f(y) S(x)` for `x ≤ y`: the hazard rate is nondecreasing. -/
def ifr (f : B) : B := allR fun x => allR fun y => imp (le x y) (le (mul (app f x) (surv f y)) (mul (app f y) (surv f x)))
def dfr (f : B) : B := allR fun x => allR fun y => imp (le x y) (le (mul (app f y) (surv f x)) (mul (app f x) (surv f y)))

/-- A function of a density, at the `x` where `d f x` holds. -/
def fnOf (name : Phrase) (d : Option (B → B → B)) (body : B → B → B) (doc : String) : Notion :=
  match d with
  | some d =>
    { name, ty := F ⟶ F, doms := [dom1 F isDensity, dom2 .real d], doc,
      value := close <| lamT F isDensity fun f => lamT .real (fun x => d f x) fun x => body f x }
  | none =>
    { name, ty := F ⟶ F, doms := [dom1 F isDensity], doc,
      value := close <| lamT F isDensity fun f => lamR fun x => body f x }
/-- A risk measure of a density with the condition `c` at a level `α`. -/
def atLevel (name : Phrase) (c : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real, doc,
    doms := [dom1 F fun f => and (isDensity f) (c f), dom2 .real quantileDom],
    value := close <| lamT F (fun f => and (isDensity f) (c f)) fun f => lamT .real (fun a => quantileDom f a) fun a => body f a }
def esDoc : String := "`(1/(1-α)) ∫_{VaR_α}^∞ x f(x) dx`, `0 < α < 1`, of a density with a finite mean"

def vocab : Vocab where
  mods := [
    { phrase := phrase!"heavy-tailed", prenominal := true, ty := F,
      pred := fPred fun f => allR fun t => imp (lt (num 0) t) (not (mgfTail f t)),
      doc := "`e^{tx} f(x)` is not integrable on `[0,∞)` for any `t > 0`" },
    { phrase := phrase!"light-tailed", prenominal := true, ty := F,
      pred := fPred fun f => exR fun t => and (lt (num 0) t) (mgfTail f t),
      doc := "`e^{tx} f(x)` is integrable on `[0,∞)` for some `t > 0`" },
    { phrase := phrase!"with increasing failure rate", prenominal := false, ty := F, pred := fPred ifr,
      doc := "`f(x) S(y) ≤ f(y) S(x)` for `x ≤ y`: `f/S` is nondecreasing (IFR)" },
    { phrase := phrase!"with decreasing failure rate", prenominal := false, ty := F, pred := fPred dfr,
      doc := "`f(y) S(x) ≤ f(x) S(y)` for `x ≤ y`: `f/S` is nonincreasing (DFR)" }]
  notions := [
    fnOf phrase!"survival function of $v$" none surv "`x ↦ ∫_x^∞ f`, `1 - F(x)`",
    fnOf phrase!"hazard rate of $v$" (some fun f x => lt (num 0) (surv f x)) (fun f x => div (app f x) (surv f x))
      "`x ↦ f(x)/S(x)`, where `S(x) > 0`",
    fnOf phrase!"hazard function of $v$" (some fun f x => lt (num 0) (surv f x)) (fun f x => div (app f x) (surv f x))
      "`x ↦ f(x)/S(x)`, where `S(x) > 0`",
    fnOf phrase!"failure rate of $v$" (some fun f x => lt (num 0) (surv f x)) (fun f x => div (app f x) (surv f x))
      "`x ↦ f(x)/S(x)`, where `S(x) > 0`",
    fnOf phrase!"cumulative hazard function of $v$" (some fun f x => lt (num 0) (surv f x)) (fun f x => neg (log (surv f x)))
      "`x ↦ -log S(x)`, where `S(x) > 0`",
    fnOf phrase!"quantile function of $v$" (some quantileDom) quantile
      "`u ↦ inf {x : F(x) ≥ u}`, `0 < u < 1` (Mathlib `ProbabilityTheory.quantile`)",
    { name := phrase!"stop-loss transform of $v$", ty := F ⟶ F, doc := "`d ↦ ∫_d^∞ (x-d) f(x) dx`, of a density with a finite mean",
      doms := [dom1 F fun f => and (isDensity f) (finiteMean f)],
      value := close <| lamT F (fun f => and (isDensity f) (finiteMean f)) fun f => lamR fun d => stopLoss f d },
    { name := phrase!"mean excess function of $v$", ty := F ⟶ F,
      doc := "`u ↦ ∫_u^∞ (x-u) f(x) dx / S(u)`, of a density with a finite mean, where `S(u) > 0`",
      doms := [dom1 F fun f => and (isDensity f) (finiteMean f), dom2 .real fun f u => lt (num 0) (surv f u)],
      value := close <| lamT F (fun f => and (isDensity f) (finiteMean f)) fun f =>
        lamT .real (fun u => lt (num 0) (surv f u)) fun u => div (stopLoss f u) (surv f u) },
    atLevel phrase!"value at risk of $v$ at level $v$" (fun _ => tt) quantile
      "the `α`-quantile `inf {x : F(x) ≥ α}`, `0 < α < 1`",
    atLevel phrase!"expected shortfall of $v$ at level $v$" finiteMean expShortfall esDoc,
    atLevel phrase!"tail value at risk of $v$ at level $v$" finiteMean expShortfall esDoc,
    atLevel phrase!"conditional value at risk of $v$ at level $v$" finiteMean expShortfall esDoc]

end Leanify.Risk
