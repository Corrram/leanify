import Leanify.Library.Core

/-! # Vocabulary: integral transforms of real functions

The transforms of a real function on the line that are again real functions: the Laplace,
Mellin and Stieltjes transforms (of a function on `[0,∞)`, with a real variable `s`), the
convolution of two functions and the autocorrelation of a function. The functions are those
of the field `realfunctions` (`Let $f$ be a continuous function.`), and a transform is used as a
function (`We write $F$ for the Laplace transform of $f$.`, then `F(s)`).

* notions: `Laplace transform of $f$` (`s ↦ ∫_0^∞ e^{-sx} f(x) dx`), `Mellin transform of
  $f$` (`s ↦ ∫_0^∞ x^{s-1} f(x) dx`), `Stieltjes transform of $f$` (`s ↦ ∫_0^∞ f(x)/(x+s) dx`,
  `s > 0`), `convolution of $f$ and $g$` (`x ↦ ∫ f(y) g(x-y) dy`), `cross-correlation of $f$
  and $g$` (`x ↦ ∫ f(y) g(y+x) dy`), `autocorrelation of $f$`;
* adjectives: `of exponential order` (`|f(x)| ≤ M e^{cx}` for all large `x`), `causal`
  (`f(x) = 0` for `x < 0`).

A transform is defined at the `s` (or the `x`) where its integrand is integrable: `F(s)` is
meaningful only there, and a claim about `F(s)` asks for it. Every meaning is a term of the
core language: the field has no constants and no model. -/

namespace Leanify.Transforms
open Build Core

abbrev F : Ty := Ty.rfun

def exp (x : B) : B := app (prim (.realFn .exp)) x
def rpow (x p : B) : B := app2 (prim .rpow) x p
def line : B := lamR fun _ => tt
def nonneg : B := lamR fun x => le (num 0) x
def pos : B := lamR fun x => lt (num 0) x
/-- `∫_S g`, and `g` is integrable on `S`. -/
def integral (s g : B) : B := app2 (prim .integralOn) s g
def integrable (s g : B) : B := app2 (prim .integrableOn) g s

def laplaceK (f s : B) : B := lamR fun x => mul (exp (neg (mul s x))) (app f x)
def mellinK (f s : B) : B := lamR fun x => mul (rpow x (sub s (num 1))) (app f x)
/-- (on `(0,∞)`, where `x + s ≠ 0` for `s > 0`) -/
def stieltjesK (f s : B) : B := lamT .real (fun x => lt (num 0) x) fun x => div (app f x) (add x s)
def convK (f g x : B) : B := lamR fun y => mul (app f y) (app g (sub x y))
def corrK (f g x : B) : B := lamR fun y => mul (app f y) (app g (add y x))

/-- A transform of one function, `s ↦ ∫_S k(f,s)`, at the `s` where `d f s` holds. -/
def of1 (name : Phrase) (d : B → B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ F, doms := [none, dom2 .real d], doc,
    value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun s => d f s) fun s => body f s }
/-- A transform of two functions, `x ↦ ∫ k(f,g,x)`, at the `x` where it is integrable. -/
def of2 (name : Phrase) (k : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ F ⟶ F, doms := [none, none, dom3 .real fun f g x => integrable line (k f g x)], doc,
    value := close <| lamT F (fun _ => tt) fun f => lamT F (fun _ => tt) fun g =>
      lamT .real (fun x => integrable line (k f g x)) fun x => integral line (k f g x) }

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p

def vocab : Vocab where
  mods := [
    { phrase := phrase!"of exponential order", prenominal := false, ty := F,
      pred := fPred fun f => exR fun m => exR fun c => exR fun t =>
        allR fun x => imp (le t x) (le (abs (app f x)) (mul m (exp (mul c x)))),
      doc := "`|f(x)| ≤ M e^{cx}` for all `x ≥ T`, for some `M`, `c`, `T`" },
    { phrase := phrase!"causal", prenominal := true, ty := F,
      pred := fPred fun f => allR fun x => imp (lt x (num 0)) (eq (app f x) (num 0)),
      doc := "`f(x) = 0` for `x < 0`" }]
  notions := [
    of1 phrase!"Laplace transform of $v$" (fun f s => integrable nonneg (laplaceK f s))
      (fun f s => integral nonneg (laplaceK f s))
      "`s ↦ ∫_0^∞ e^{-sx} f(x) dx`, at the `s` where the integrand is integrable",
    of1 phrase!"Mellin transform of $v$" (fun f s => integrable pos (mellinK f s))
      (fun f s => integral pos (mellinK f s))
      "`s ↦ ∫_0^∞ x^{s-1} f(x) dx`, at the `s` where the integrand is integrable (Mathlib `mellin`)",
    of1 phrase!"Stieltjes transform of $v$" (fun f s => and (lt (num 0) s) (integrable pos (stieltjesK f s)))
      (fun f s => integral pos (stieltjesK f s))
      "`s ↦ ∫_0^∞ f(x)/(x+s) dx`, at the `s > 0` where the integrand is integrable",
    of2 phrase!"convolution of $v$ and $v$" convK
      "`x ↦ ∫ f(y) g(x-y) dy`, at the `x` where the integrand is integrable (Mathlib `convolution`)",
    of2 phrase!"cross-correlation of $v$ and $v$" corrK
      "`x ↦ ∫ f(y) g(y+x) dy`, at the `x` where the integrand is integrable",
    { name := phrase!"autocorrelation of $v$", ty := F ⟶ F, doc := "`x ↦ ∫ f(y) f(y+x) dy`, where integrable",
      doms := [none, dom2 .real fun f x => integrable line (corrK f f x)],
      value := close <| lamT F (fun _ => tt) fun f =>
        lamT .real (fun x => integrable line (corrK f f x)) fun x => integral line (corrK f f x) }]

end Leanify.Transforms
