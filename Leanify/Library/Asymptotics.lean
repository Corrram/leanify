import Leanify.Library.Core

/-! # Vocabulary: asymptotics at infinity

How real functions behave as their argument tends to `∞`: comparisons of two functions
(`$f$ is asymptotically equivalent to $g$`), growth classes, and regular variation, as in
extreme value theory and the tails of distributions. The functions are those of the field
`realfunctions` (`Let $f$ and $g$ be continuous functions.`).

* comparisons, with the other function: `asymptotically equivalent to $g$` (`f/g → 1`),
  `dominated by $g$` (`f = O(g)`), `negligible compared to $g$` (`f = o(g)`), `of the same
  order as $g$` (`f = Θ(g)`);
* adjectives: `eventually positive`, `bounded at infinity`, `of polynomial growth`, `of at
  most exponential growth`, `slowly varying`, `regularly varying with index $\alpha$`;
* notions: the limit of a function at infinity and at minus infinity (where it exists), and
  the index of regular variation of a regularly varying function.

Every comparison is written with `ε` and a threshold, without quotients, so that it is
meaningful for every pair of functions (`|f(x) - g(x)| ≤ ε|g(x)|` for all large `x`, for
every `ε > 0`). Every meaning is a term of the core language: the field has no constants
and no model. -/

namespace Leanify.Asymptotics
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def rpow (x p : B) : B := app2 (prim .rpow) x p
def exp (x : B) : B := app (prim (.realFn .exp)) x

/-- `body x` for all `x` from some threshold on. -/
def eventually (body : B → B) : B := exR fun m => allR fun x => imp (le m x) (body x)
/-- For every `ε > 0`, eventually `body ε x`. -/
def forEps (body : B → B → B) : B := allR fun e => imp (lt (num 0) e) (eventually fun x => body e x)

def equivalent (f g : B) : B :=
  forEps fun e x => le (abs (sub (app f x) (app g x))) (mul e (abs (app g x)))
def bigO (f g : B) : B :=
  exR fun c => eventually fun x => le (abs (app f x)) (mul c (abs (app g x)))
def littleO (f g : B) : B := forEps fun e x => le (abs (app f x)) (mul e (abs (app g x)))
def theta (f g : B) : B :=
  exR fun c => exR fun d => and (and (lt (num 0) c) (lt (num 0) d))
    (eventually fun x => and (le (mul c (abs (app g x))) (abs (app f x))) (le (abs (app f x)) (mul d (abs (app g x)))))
def eventuallyPos (f : B) : B := eventually fun x => lt (num 0) (app f x)
/-- `f(tx)/f(x) → t^α` for every `t > 0`, `f` eventually positive. -/
def regVar (a f : B) : B :=
  and (eventuallyPos f) (allR fun t => imp (lt (num 0) t)
    (forEps fun e x => le (abs (sub (app f (mul t x)) (mul (rpow t a) (app f x)))) (mul e (app f x))))
/-- `f(x) → l` as `x → ∞`. -/
def tendsTo (f l : B) : B := forEps fun e x => le (abs (sub (app f x) l)) e
def hasLimit (f : B) : B := exR fun l => tendsTo f l
def hasLimitNeg (f : B) : B := exR fun l => tendsTo (lamR fun x => app f (neg x)) l

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pred : Tm) (doc : String) : Modifier := { phrase := p, prenominal := true, ty := F, pred, doc }
/-- A comparison with another function `g` (`P g f`, the other function first). -/
def cmp (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamT F (fun _ => tt) fun g => lamT F (fun _ => tt) fun f => body f g }

def vocab : Vocab where
  mods := [
    cmp phrase!"asymptotically equivalent to $v$" equivalent "`f(x)/g(x) → 1` as `x → ∞`: `|f - g| ≤ ε|g|` eventually, for every `ε > 0` (Mathlib `Asymptotics.IsEquivalent`)",
    cmp phrase!"dominated by $v$" bigO "`|f| ≤ C|g|` eventually: `f = O(g)` (Mathlib `Asymptotics.IsBigO`)",
    cmp phrase!"negligible compared to $v$" littleO "`|f| ≤ ε|g|` eventually, for every `ε > 0`: `f = o(g)` (Mathlib `Asymptotics.IsLittleO`)",
    cmp phrase!"of the same order as $v$" theta "`c|g| ≤ |f| ≤ C|g|` eventually, `c, C > 0`: `f = Θ(g)` (Mathlib `Asymptotics.IsTheta`)",
    adj phrase!"eventually positive" (fPred eventuallyPos) "`f(x) > 0` for all large `x`",
    adj phrase!"bounded at infinity" (fPred fun f => exR fun c => eventually fun x => le (abs (app f x)) c)
      "`|f(x)| ≤ C` for all large `x`",
    { phrase := phrase!"bounded at infinity", prenominal := false, ty := F,
      pred := fPred fun f => exR fun c => eventually fun x => le (abs (app f x)) c, doc := "after the noun" },
    { phrase := phrase!"of polynomial growth", prenominal := false, ty := F,
      pred := fPred fun f => exR fun c => exR fun k => eventually fun x =>
        and (le (num 1) x) (le (abs (app f x)) (mul c (rpow x k))),
      doc := "`|f(x)| ≤ C x^k` for all large `x`" },
    { phrase := phrase!"of at most exponential growth", prenominal := false, ty := F,
      pred := fPred fun f => exR fun c => exR fun a => eventually fun x => le (abs (app f x)) (mul c (exp (mul a x))),
      doc := "`|f(x)| ≤ C e^{ax}` for all large `x`" },
    adj phrase!"slowly varying" (fPred fun f => regVar (num 0) f)
      "eventually positive, `f(tx)/f(x) → 1` for every `t > 0` (Karamata; Mathlib has no counterpart)",
    { phrase := phrase!"regularly varying with index $v$", prenominal := false, ty := F,
      pred := close <| lamR fun a => lamT F (fun _ => tt) fun f => regVar a f,
      doc := "eventually positive, `f(tx)/f(x) → t^α` for every `t > 0`" }]
  notions := [
    { name := phrase!"limit of $v$ at infinity", ty := F ⟶ .real, doms := [dom1 F hasLimit],
      doc := "`lim_{x→∞} f(x)`, of a function that has one (Mathlib `Filter.Tendsto f atTop`)",
      value := close <| lamT F hasLimit fun f => theR fun l => tendsTo f l },
    { name := phrase!"limit of $v$ at minus infinity", ty := F ⟶ .real, doms := [dom1 F hasLimitNeg],
      doc := "`lim_{x→-∞} f(x)`, of a function that has one",
      value := close <| lamT F hasLimitNeg fun f => theR fun l => tendsTo (lamR fun x => app f (neg x)) l },
    { name := phrase!"index of regular variation of $v$", ty := F ⟶ .real,
      doms := [dom1 F fun f => exR fun a => regVar a f],
      doc := "the `α` with `f(tx)/f(x) → t^α`, of a regularly varying function",
      value := close <| lamT F (fun f => exR fun a => regVar a f) fun f => theR fun a => regVar a f }]

end Leanify.Asymptotics
