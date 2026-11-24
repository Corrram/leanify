import Leanify.Library.Core

/-! # Vocabulary: iteration of real maps

One-dimensional discrete dynamics: the iterates `f^n = f ∘ … ∘ f` of a real function, the
orbits of points, fixed and periodic points and their stability. The maps are the
functions of the field `analysis` (`Let $f$ be a continuous function.`), the points real
numbers (`$p$ is an attracting fixed point of $f$`).

* adjectives of points, with the map: `fixed point of $f$`, `periodic point of $f$`,
  `periodic point of $f$ of period $n$` (`f^n(x) = x`), `periodic point of $f$ of least
  period $n$`, `eventually periodic point of $f$`, and of a fixed point where `f` is
  differentiable: `attracting` (`|f'(x)| < 1`), `superattracting` (`f'(x) = 0`), `repelling`
  (`|f'(x)| > 1`) and `neutral` (`|f'(x)| = 1`);
* notions: the `n`th iterate of `f` (the identity for `n = 0`), the orbit of a point, the
  sets of fixed and of periodic points, the least period of a periodic point, and the
  Lyapunov exponent `lim_{n→∞} (1/n) log |(f^n)'(x)|` (where `f^n` is differentiable at `x`
  for every `n` and the limit exists).

The iterate is a constant, Mathlib's `Nat.iterate` (`Leanify/Library/DynamicsModel.lean`);
the rest is a term of the core language. -/

namespace Leanify.Dynamics
open Build Core

abbrev F : Ty := Ty.rfun

def iter (n f : B) : B := app2 (const 0) n f
def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def log (x : B) : B := app (prim (.realFn .log)) x
def nat (n : B) : B := and (isInt n) (le (num 0) n)
def posNat (n : B) : B := and (isInt n) (le (num 1) n)

def isFixed (f x : B) : B := eq (app f x) x
def periodWith (f n x : B) : B := and (posNat n) (eq (app (iter n f) x) x)
def isPeriodic (f x : B) : B := exR fun n => periodWith f n x
def leastPeriod (f n x : B) : B :=
  and (periodWith f n x) (allR fun k => imp (and (posNat k) (lt k n)) (ne (app (iter k f) x) x))
/-- A fixed point where `f` has a derivative `d` with `cond d`. -/
def fixedWith (cond : B → B) (f x : B) : B :=
  and (isFixed f x) (exR fun d => and (hasDeriv f x d) (cond d))

/-- `n ↦ (1/n) log |(f^n)'(x)|`, for `n ≥ 1`. -/
def lyapTerms (f x : B) : B :=
  lamT .real (fun n => posNat n) fun n => div (log (abs (theR fun d => hasDeriv (iter n f) x d))) n
def posNatSet : B := lamR fun n => posNat n
/-- Every `f^n` (`n ≥ 1`) has a derivative at `x`, and the sequence has a limit. -/
def lyapDom (f x : B) : B :=
  and (allR fun n => imp (posNat n) (exR fun d => and (hasDeriv (iter n f) x d)
      (allR fun e => imp (hasDeriv (iter n f) x e) (eq e d))))
    (app2 (prim .limTopConv) posNatSet (lyapTerms f x))

def ofFn (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := .real, doc, pred := close <| lamT F (fun _ => tt) fun f => lamR fun x => body f x }
def ofFnN (p : Phrase) (body : B → B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := .real, doc,
    pred := close <| lamT F (fun _ => tt) fun f => lamR fun n => lamR fun x => body f n x }
def ofF (name : Phrase) (ty : Ty) (body : B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ ty, doms := [none], doc, value := close <| lamT F (fun _ => tt) body }

def vocab : Vocab where
  consts := [.real ⟶ F ⟶ F]
  constNames := [w!"#2^{#1}"]
  constLean := [w!"Leanify.Dynamics.iterate"]
  modules := [w!"Leanify.Library.DynamicsModel"]
  mods := [
    ofFn phrase!"fixed point of $v$" isFixed "`f(x) = x` (Mathlib `Function.IsFixedPt`)",
    ofFn phrase!"periodic point of $v$" isPeriodic "`f^n(x) = x` for some `n ≥ 1` (Mathlib `Function.IsPeriodicPt`)",
    ofFnN phrase!"periodic point of $v$ of period $v$" periodWith "`f^n(x) = x`, `n ≥ 1` (Mathlib `Function.IsPeriodicPt`)",
    ofFnN phrase!"periodic point of $v$ of least period $v$" leastPeriod
      "`f^n(x) = x` and `f^k(x) ≠ x` for `1 ≤ k < n` (Mathlib `Function.minimalPeriod`)",
    ofFnN phrase!"periodic point of $v$ of minimal period $v$" leastPeriod "`n` is the least period",
    ofFnN phrase!"periodic point of $v$ of prime period $v$" leastPeriod "`n` is the least period",
    ofFn phrase!"eventually periodic point of $v$"
      (fun f x => exR fun m => and (nat m) (isPeriodic f (app (iter m f) x))) "`f^m(x)` is periodic for some `m ≥ 0`",
    ofFn phrase!"attracting fixed point of $v$" (fixedWith fun d => lt (abs d) (num 1)) "`f(x) = x`, `|f'(x)| < 1`",
    ofFn phrase!"superattracting fixed point of $v$" (fixedWith fun d => eq d (num 0)) "`f(x) = x`, `f'(x) = 0`",
    ofFn phrase!"repelling fixed point of $v$" (fixedWith fun d => lt (num 1) (abs d)) "`f(x) = x`, `|f'(x)| > 1`",
    ofFn phrase!"neutral fixed point of $v$" (fixedWith fun d => eq (abs d) (num 1)) "`f(x) = x`, `|f'(x)| = 1`"]
  notions := [
    { name := phrase!"$v$th iterate of $v$", ty := .real ⟶ F ⟶ F, doms := [dom1 .real nat, none],
      doc := "`f ∘ … ∘ f`, `n` times; the identity for `n = 0` (Mathlib `Nat.iterate`)", value := .const 0 },
    { name := phrase!"orbit of $v$ under $v$", ty := .real ⟶ F ⟶ .real ⟶ .prop, doms := [none, none],
      doc := "`{f^n(x) : n ≥ 0}` (Mathlib `Set.range (fun n => f^[n] x)`)",
      value := close <| lamR fun x => lamT F (fun _ => tt) fun f => lamR fun y => exR fun n => and (nat n) (eq y (app (iter n f) x)) },
    { name := phrase!"set of fixed points of $v$", ty := F ⟶ .real ⟶ .prop, doms := [none],
      doc := "`{x : f(x) = x}` (Mathlib `Function.fixedPoints`)",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun x => isFixed f x },
    { name := phrase!"set of periodic points of $v$", ty := F ⟶ .real ⟶ .prop, doms := [none],
      doc := "`{x : f^n(x) = x for some n ≥ 1}` (Mathlib `Function.periodicPts`)",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun x => isPeriodic f x },
    { name := phrase!"least period of $v$ under $v$", ty := .real ⟶ F ⟶ .real, doms := [none, dom2 F fun x f => isPeriodic f x],
      doc := "the least `n ≥ 1` with `f^n(x) = x`, of a periodic point (Mathlib `Function.minimalPeriod`)",
      value := close <| lamR fun x => lamT F (fun f => isPeriodic f x) fun f => theR fun n => leastPeriod f n x },
    { name := phrase!"Lyapunov exponent of $v$ at $v$", ty := F ⟶ .real ⟶ .real, doms := [none, dom2 .real lyapDom],
      doc := "`lim_{n→∞} (1/n) log |(f^n)'(x)|`, where every `f^n` is differentiable at `x` and the limit exists",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun x => lyapDom f x) fun x =>
        app2 (prim .limTop) posNatSet (lyapTerms f x) }]

end Leanify.Dynamics
