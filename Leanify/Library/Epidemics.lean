import Leanify.Library.Core

/-! # Vocabulary: epidemic models

The threshold quantities of compartmental epidemic models (`We write $R_0$ for the basic
reproduction number of the SIR model with transmission rate $\beta$ and recovery rate
$\gamma$.`), and the solutions of the SIS model.

* notions: the basic reproduction number `β/γ` of the SIR model (and `β/(γ+μ)` with
  mortality `μ`), the herd immunity threshold `1 - 1/R₀`, the final size of an SIR epidemic
  (the `z ∈ (0,1)` with `z = 1 - e^{-R₀ z}`, for `R₀ > 1`), the doubling time `log 2/r` of
  exponential growth at rate `r`, the endemic equilibrium `1 - 1/R₀` of the SIS model, the
  critical vaccination coverage `(1 - 1/R₀)/e` for a vaccine of efficacy `e`;
* adjectives of functions: `solution of the SIS model with transmission rate $\beta$ and
  recovery rate $\gamma$` (`i' = β i (1 - i) - γ i`), `solution of the exponential growth
  equation with rate $r$` (`y' = r y`).

Every meaning is a term of the core language. -/

namespace Leanify.Epidemics
open Build Core

abbrev F : Ty := Ty.rfun

def pos (x : B) : B := lt (num 0) x
def log (x : B) : B := app (prim (.realFn .log)) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diff (f : B) : B := allR fun t => exR fun d => hasDeriv f t d
def any (_ : B) : B := tt
def gtOne (r : B) : B := lt (num 1) r

def vocab : Vocab where
  mods := [
    { phrase := phrase!"solution of the SIS model with transmission rate $v$ and recovery rate $v$", prenominal := false, ty := F,
      pred := close <| lamR fun b => lamR fun g => lamT F any fun i =>
        and (and (pos b) (pos g)) (and (diff i) (allR fun t => eq (deriv i t) (sub (mul (mul b (app i t)) (sub (num 1) (app i t))) (mul g (app i t))))),
      doc := "`i' = β i (1 - i) - γ i` everywhere (the infected fraction)" },
    { phrase := phrase!"solution of the exponential growth equation with rate $v$", prenominal := false, ty := F,
      pred := close <| lamR fun r => lamT F any fun y => and (diff y) (allR fun t => eq (deriv y t) (mul r (app y t))),
      doc := "`y' = r y` everywhere" }]
  notions := [
    { name := phrase!"basic reproduction number of the SIR model with transmission rate $v$ and recovery rate $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real pos], doc := "`R₀ = β/γ`",
      value := close <| lamT .real pos fun b => lamT .real pos fun g => div b g },
    { name := phrase!"basic reproduction number of the SIR model with transmission rate $v$, recovery rate $v$ and mortality $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real pos, dom1 .real fun m => le (num 0) m],
      doc := "`R₀ = β/(γ + μ)`, with births and deaths at rate `μ`",
      value := close <| lamT .real pos fun b => lamT .real pos fun g => lamT .real (fun m => le (num 0) m) fun m => div b (add g m) },
    { name := phrase!"herd immunity threshold for the basic reproduction number $v$", ty := .real ⟶ .real, doms := [dom1 .real gtOne],
      doc := "`1 - 1/R₀`, `R₀ > 1`", value := close <| lamT .real gtOne fun r => sub (num 1) (div (num 1) r) },
    { name := phrase!"final size of the epidemic with basic reproduction number $v$", ty := .real ⟶ .real, doms := [dom1 .real gtOne],
      doc := "the `z ∈ (0,1)` with `z = 1 - e^{-R₀ z}` (the final size equation), `R₀ > 1`",
      value := close <| lamT .real gtOne fun r => theR fun z => and (and (lt (num 0) z) (lt z (num 1))) (eq z (sub (num 1) (exp (neg (mul r z))))) },
    { name := phrase!"doubling time for the growth rate $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`log 2/r`", value := close <| lamT .real pos fun r => div (log (num 2)) r },
    { name := phrase!"endemic equilibrium of the SIS model with basic reproduction number $v$", ty := .real ⟶ .real, doms := [dom1 .real gtOne],
      doc := "`1 - 1/R₀`, the infected fraction at equilibrium", value := close <| lamT .real gtOne fun r => sub (num 1) (div (num 1) r) },
    { name := phrase!"critical vaccination coverage for the basic reproduction number $v$ and efficacy $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real gtOne, dom1 .real fun e => and (lt (num 0) e) (le e (num 1))], doc := "`(1 - 1/R₀)/e`",
      value := close <| lamT .real gtOne fun r => lamT .real (fun e => and (lt (num 0) e) (le e (num 1))) fun e =>
        div (sub (num 1) (div (num 1) r)) e }]

end Leanify.Epidemics
