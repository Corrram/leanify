import Leanify.Library.Core

/-! # Vocabulary: optimization of real functions

Minimizers, extreme values and the convex analysis of a real function on the line. The
functions are those of the field `analysis` (`Let $f$ be a convex function.`), and the
points are real numbers (`$x$ is a local minimizer of $f$`).

* adjectives of functions: `strongly convex`, `$\mu$-strongly convex`, `$L$-smooth`,
  `coercive`, `quasiconvex`, `bounded below`, `bounded above`;
* adjectives of points, with the function: `minimizer of $f$`, `maximizer of $f$` (global),
  `local minimizer of $f$`, `local maximizer of $f$`, `strict local minimizer of $f$`,
  `minimizer of $f$ on $[a,b]$`, `stationary point of $f$`;
* notions: the minimum and maximum of a function (where they are attained), on the line and
  on `[a,b]`, its infimum and supremum (where bounded), the minimizer (where there is exactly
  one), the set of minimizers, the convex conjugate `f^*(y) = sup_x (xy - f(x))` (where the
  supremum is finite), the Moreau envelope and the proximal operator with a parameter
  `λ > 0`.

A value that is a supremum or an infimum, or the one point with a property, is a
description: it is defined only where exactly one number has the property, so that a
claim about the minimum of `f` is meaningful only if `f` attains it. Every meaning is a
term of the core language: the field has no constants and no model. -/

namespace Leanify.Optimization
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def convex (g : B) : B := app2 (prim (.fnProp .convex)) g line
/-- `f` has derivative `d` at `x`. -/
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def differentiable (f : B) : B := allR fun x => exR fun d => hasDeriv f x d

def stronglyConvexWith (m f : B) : B :=
  and (lt (num 0) m) (convex (lamR fun x => sub (app f x) (mul (div m (num 2)) (mul x x))))
def smoothWith (l f : B) : B :=
  and (and (le (num 0) l) (differentiable f))
    (allR fun x => allR fun y => allR fun dx => allR fun dy =>
      imp (and (hasDeriv f x dx) (hasDeriv f y dy)) (le (abs (sub dx dy)) (mul l (abs (sub x y)))))
def boundedBelow (f : B) : B := exR fun m => allR fun x => le m (app f x)
def boundedAbove (f : B) : B := exR fun m => allR fun x => le (app f x) m

def isMin (f x : B) : B := allR fun y => le (app f x) (app f y)
def isMax (f x : B) : B := allR fun y => le (app f y) (app f x)
def near (x y d : B) : B := lt (abs (sub y x)) d
def isLocalMin (f x : B) : B := exR fun d => and (lt (num 0) d) (allR fun y => imp (near x y d) (le (app f x) (app f y)))
def isLocalMax (f x : B) : B := exR fun d => and (lt (num 0) d) (allR fun y => imp (near x y d) (le (app f y) (app f x)))
def inI (a b x : B) : B := and (le a x) (le x b)

/-- The greatest lower bound of the values `g(x)`. -/
def inf (g : B) : B := theR fun m => and (allR fun x => le m (app g x))
  (allR fun e => imp (lt (num 0) e) (exR fun x => lt (app g x) (add m e)))
def sup (g : B) : B := theR fun m => and (allR fun x => le (app g x) m)
  (allR fun e => imp (lt (num 0) e) (exR fun x => lt (sub m e) (app g x)))

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def fmod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred, doc }
/-- A property of a point `x` with the function (`P f x`, the function first). -/
def ofFn (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := .real, doc, pred := close <| lamT F (fun _ => tt) fun f => lamR fun x => body f x }

/-- A notion of a function, defined where `d` holds. -/
def ofF (name : Phrase) (ty : Ty) (d : Option (B → B)) (body : B → B) (doc : String) : Notion :=
  match d with
  | some d => { name, ty := F ⟶ ty, doms := [dom1 F d], doc, value := close <| lamT F d body }
  | none => { name, ty := F ⟶ ty, doms := [none], doc, value := close <| lamT F (fun _ => tt) body }
def posP (l : B) : B := lt (num 0) l
def exUnique (p : B → B) : B := exR fun m => and (p m) (allR fun m' => imp (p m') (eq m' m))

def attainsMin (f : B) : B := exR fun x => isMin f x
def attainsMax (f : B) : B := exR fun x => isMax f x
def attainsMinOn (f a b : B) : B := and (le a b) (exR fun x => and (inI a b x) (allR fun y => imp (inI a b y) (le (app f x) (app f y))))
def attainsMaxOn (f a b : B) : B := and (le a b) (exR fun x => and (inI a b x) (allR fun y => imp (inI a b y) (le (app f y) (app f x))))
/-- A notion of a function on `[a,b]`, defined where `d f a b` holds. -/
def ofFab (name : Phrase) (d : B → B → B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real, doms := [none, none, dom3 .real d], doc,
    value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamT .real (fun b => d f a b) fun b => body f a b }
/-- `x y - f(x)` is bounded above in `x`. -/
def conjDom (f y : B) : B := exR fun m => allR fun x => le (sub (mul x y) (app f x)) m
/-- `z ↦ f(z) + (y - z)²/(2λ)`. -/
def moreauFn (f l y : B) : B := lamR fun z => add (app f z) (div (mul (sub y z) (sub y z)) (mul (num 2) l))
def moreauDom (f l y : B) : B := exR fun m => allR fun z => le m (app (moreauFn f l y) z)
def proxDom (f l y : B) : B := exUnique fun z => isMin (moreauFn f l y) z

/-- `inf_z (f(z) + (y - z)²/(2λ))`. -/
def moreauAt (f l y : B) : B := inf (moreauFn f l y)

def vocab : Vocab where
  mods := [
    fmod phrase!"strongly convex" true (fPred fun f => exR fun m => stronglyConvexWith m f)
      "`f - (μ/2)x²` is convex for some `μ > 0` (Mathlib `StrongConvexOn`)",
    fmod phrase!"$v$-strongly convex" true (close <| lamR fun m => lamT F (fun _ => tt) fun f => stronglyConvexWith m f)
      "`f - (μ/2)x²` is convex, `μ > 0` (Mathlib `StrongConvexOn`)",
    fmod phrase!"$v$-smooth" true (close <| lamR fun l => lamT F (fun _ => tt) fun f => smoothWith l f)
      "differentiable, with an `L`-Lipschitz derivative",
    fmod phrase!"coercive" true
      (fPred fun f => allR fun m => exR fun r => allR fun x => imp (le r (abs x)) (le m (app f x)))
      "`f(x) → ∞` as `|x| → ∞`",
    fmod phrase!"quasiconvex" true
      (fPred fun f => allR fun x => allR fun y => allR fun t => imp (and (le (num 0) t) (le t (num 1)))
        (le (app f (add (mul t x) (mul (sub (num 1) t) y))) (app2 (prim .max) (app f x) (app f y))))
      "`f(tx + (1-t)y) ≤ max(f(x), f(y))` (Mathlib `QuasiconvexOn`)",
    fmod phrase!"bounded below" true (fPred boundedBelow) "`m ≤ f(x)` for some `m` (Mathlib `BddBelow (Set.range f)`)",
    fmod phrase!"bounded below" false (fPred boundedBelow) "after the noun: `a function $f$ bounded below`",
    fmod phrase!"bounded above" true (fPred boundedAbove) "`f(x) ≤ M` for some `M`",
    fmod phrase!"bounded above" false (fPred boundedAbove) "after the noun",
    ofFn phrase!"minimizer of $v$" isMin "`f(x) ≤ f(y)` for every `y` (Mathlib `IsMinOn`)",
    ofFn phrase!"global minimizer of $v$" isMin "`f(x) ≤ f(y)` for every `y`",
    ofFn phrase!"maximizer of $v$" isMax "`f(y) ≤ f(x)` for every `y` (Mathlib `IsMaxOn`)",
    ofFn phrase!"global maximizer of $v$" isMax "`f(y) ≤ f(x)` for every `y`",
    ofFn phrase!"local minimizer of $v$" isLocalMin "`f(x) ≤ f(y)` for `y` near `x` (Mathlib `IsLocalMin`)",
    ofFn phrase!"local maximizer of $v$" isLocalMax "`f(y) ≤ f(x)` for `y` near `x` (Mathlib `IsLocalMax`)",
    ofFn phrase!"strict local minimizer of $v$"
      (fun f x => exR fun d => and (lt (num 0) d)
        (allR fun y => imp (and (near x y d) (ne y x)) (lt (app f x) (app f y))))
      "`f(x) < f(y)` for `y ≠ x` near `x`",
    ofFn phrase!"stationary point of $v$" (fun f x => hasDeriv f x (num 0)) "`f'(x) = 0`",
    { phrase := phrase!"minimizer of $v$ on $[v,v]$", prenominal := false, ty := .real,
      doc := "`x ∈ [a,b]` and `f(x) ≤ f(y)` for every `y ∈ [a,b]`",
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamR fun b => lamR fun x =>
        and (inI a b x) (allR fun y => imp (inI a b y) (le (app f x) (app f y))) },
    { phrase := phrase!"maximizer of $v$ on $[v,v]$", prenominal := false, ty := .real,
      doc := "`x ∈ [a,b]` and `f(y) ≤ f(x)` for every `y ∈ [a,b]`",
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamR fun b => lamR fun x =>
        and (inI a b x) (allR fun y => imp (inI a b y) (le (app f y) (app f x))) }]
  notions := [
    ofF phrase!"minimum of $v$" .real (some attainsMin)
      (fun f => theR fun m => and (exR fun x => eq (app f x) m) (allR fun y => le m (app f y)))
      "the least value of `f`, of a function that attains it",
    ofF phrase!"maximum of $v$" .real (some attainsMax)
      (fun f => theR fun m => and (exR fun x => eq (app f x) m) (allR fun y => le (app f y) m))
      "the greatest value of `f`, of a function that attains it",
    ofF phrase!"infimum of $v$" .real (some boundedBelow) inf
      "the greatest lower bound of the values, of a function bounded below (Mathlib `iInf`)",
    ofF phrase!"supremum of $v$" .real (some boundedAbove) sup
      "the least upper bound of the values, of a function bounded above (Mathlib `iSup`)",
    ofFab phrase!"minimum of $v$ on $[v,v]$" attainsMinOn
      (fun f a b => theR fun m => and (exR fun x => and (inI a b x) (eq (app f x) m))
        (allR fun y => imp (inI a b y) (le m (app f y))))
      "the least value of `f` on `[a,b]`, `a ≤ b`, where it is attained",
    ofFab phrase!"maximum of $v$ on $[v,v]$" attainsMaxOn
      (fun f a b => theR fun m => and (exR fun x => and (inI a b x) (eq (app f x) m))
        (allR fun y => imp (inI a b y) (le (app f y) m)))
      "the greatest value of `f` on `[a,b]`, `a ≤ b`, where it is attained",
    ofF phrase!"unique minimizer of $v$" .real (some fun f => exUnique fun x => isMin f x) (fun f => theR fun x => isMin f x)
      "the point where `f` is least, of a function with exactly one such point (Mathlib `argmin`)",
    ofF phrase!"set of minimizers of $v$" (.real ⟶ .prop) none (fun f => lamR fun x => isMin f x)
      "`{x : f(x) ≤ f(y) for every y}`",
    ofF phrase!"set of maximizers of $v$" (.real ⟶ .prop) none (fun f => lamR fun x => isMax f x)
      "`{x : f(y) ≤ f(x) for every y}`",
    { name := phrase!"convex conjugate of $v$", ty := F ⟶ F, doms := [none, dom2 .real conjDom],
      doc := "`y ↦ sup_x (xy - f(x))`, at the `y` where the supremum is finite (the Legendre–Fenchel transform)",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun y => conjDom f y)
        fun y => sup (lamR fun x => sub (mul x y) (app f x)) },
    { name := phrase!"Legendre transform of $v$", ty := F ⟶ F, doms := [none, dom2 .real conjDom],
      doc := "the convex conjugate `y ↦ sup_x (xy - f(x))`",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun y => conjDom f y)
        fun y => sup (lamR fun x => sub (mul x y) (app f x)) },
    { name := phrase!"Moreau envelope of $v$ with parameter $v$", ty := F ⟶ .real ⟶ F,
      doms := [none, dom1 .real posP, dom3 .real moreauDom],
      doc := "`y ↦ inf_z (f(z) + (y - z)²/(2λ))`, `λ > 0`, where the infimum is finite",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real posP fun l =>
        lamT .real (fun y => moreauDom f l y) fun y => moreauAt f l y },
    { name := phrase!"proximal operator of $v$ with parameter $v$", ty := F ⟶ .real ⟶ F,
      doms := [none, dom1 .real posP, dom3 .real proxDom],
      doc := "`y ↦ argmin_z (f(z) + (y - z)²/(2λ))`, `λ > 0`, where there is exactly one minimizer",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real posP fun l =>
        lamT .real (fun y => proxDom f l y) fun y => theR fun z => isMin (moreauFn f l y) z }]

end Leanify.Optimization
