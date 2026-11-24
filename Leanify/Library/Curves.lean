import Leanify.Library.Core

/-! # Vocabulary: plane curves

Differential geometry of curves in the plane: a parametrized curve given by its coordinate
functions `x` and `y` (`the curvature of the curve with coordinates $x$ and $y$ at $t$`), the
graph of a function, and a curve in polar coordinates `r = r(θ)`.

* notions: the speed `√(x'² + y'²)`, the signed curvature `(x'y'' - y'x'')/(x'² + y'²)^{3/2}`,
  the length `∫_a^b √(x'² + y'²)` and the signed area `½ ∫_a^b (x y' - y x')` of a
  parametrized curve; the curvature `f''/(1 + f'²)^{3/2}` and the radius of curvature of a
  graph; the area `½ ∫_a^b r²` and the length `∫_a^b √(r² + r'²)` of a polar curve;
* adjectives of parameters: `regular point of the curve with coordinates $x$ and $y$`
  (`x'² + y'² > 0`), `singular point of …` (`x' = y' = 0`).

Derivatives are descriptions (the derivative where it exists), integrals those of the core
language; each quantity is defined where its derivatives exist and its integrand is
integrable. -/

namespace Leanify.Curves
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def diff (f : B) : B := allR fun x => diffAt f x
def d1 (f : B) : B := lamR fun t => deriv f t
def d2 (f t : B) : B := deriv (d1 f) t
def twiceAt (f t : B) : B := and (diff f) (diffAt (d1 f) t)
def rpow (x y : B) : B := app2 (prim .rpow) x y
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def threeHalves (x : B) : B := rpow x (div (num 3) (num 2))
def sq (x : B) : B := mul x x
def speed2 (x y t : B) : B := add (sq (deriv x t)) (sq (deriv y t))
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def integrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b
def lengthIntegrand (x y : B) : B := lamR fun t => sqrt (speed2 x y t)
def areaIntegrand (x y : B) : B := lamR fun t => sub (mul (app x t) (deriv y t)) (mul (app y t) (deriv x t))
def curvDom (x y t : B) : B := and (twiceAt x t) (and (twiceAt y t) (ne (speed2 x y t) (num 0)))
def curv (x y t : B) : B :=
  div (sub (mul (deriv x t) (d2 y t)) (mul (deriv y t) (d2 x t))) (threeHalves (speed2 x y t))
def onAB (x y a b : B) (g : B) : B := and (le a b) (and (diff x) (and (diff y) (integrable g a b)))
def polarLen (r : B) : B := lamR fun t => sqrt (add (sq (app r t)) (sq (deriv r t)))
def polarArea (r : B) : B := lamR fun t => sq (app r t)
def graphCurv (f x : B) : B := div (d2 f x) (threeHalves (add (num 1) (sq (deriv f x))))

/-- A notion of a curve with coordinates `x`, `y` on `[a,b]`. -/
def curveAB (name : Phrase) (g : B → B → B) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ F ⟶ .real ⟶ .real ⟶ .real, doc,
    doms := [none, none, none, dom4 .real fun x y a b => onAB x y a b (g x y)],
    value := close <| lamT F (fun _ => tt) fun x => lamT F (fun _ => tt) fun y => lamR fun a =>
      lamT .real (fun b => onAB x y a b (g x y)) fun b => body x y a b }
def polarDom (needsDiff : Bool) (g : B → B) (r a b : B) : B :=
  and (le a b) (if needsDiff then and (diff r) (integrable (g r) a b) else integrable (g r) a b)
def polarAB (name : Phrase) (needsDiff : Bool) (g : B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real, doc,
    doms := [none, none, dom3 .real (polarDom needsDiff g)],
    value := close <| lamT F (fun _ => tt) fun r => lamR fun a =>
      lamT .real (fun b => polarDom needsDiff g r a b) fun b => body r a b }

def vocab : Vocab where
  mods := [
    { phrase := phrase!"regular point of the curve with coordinates $v$ and $v$", prenominal := false, ty := .real,
      pred := close <| lamT F (fun _ => tt) fun x => lamT F (fun _ => tt) fun y => lamR fun t =>
        and (and (diffAt x t) (diffAt y t)) (lt (num 0) (speed2 x y t)),
      doc := "`x`, `y` differentiable at `t` and `x'(t)² + y'(t)² > 0`" },
    { phrase := phrase!"singular point of the curve with coordinates $v$ and $v$", prenominal := false, ty := .real,
      pred := close <| lamT F (fun _ => tt) fun x => lamT F (fun _ => tt) fun y => lamR fun t =>
        and (hasDeriv x t (num 0)) (hasDeriv y t (num 0)),
      doc := "`x'(t) = y'(t) = 0`" }]
  notions := [
    { name := phrase!"speed of the curve with coordinates $v$ and $v$ at $v$", ty := F ⟶ F ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun x y t => and (diffAt x t) (diffAt y t)],
      doc := "`√(x'(t)² + y'(t)²)`",
      value := close <| lamT F (fun _ => tt) fun x => lamT F (fun _ => tt) fun y =>
        lamT .real (fun t => and (diffAt x t) (diffAt y t)) fun t => sqrt (speed2 x y t) },
    { name := phrase!"curvature of the curve with coordinates $v$ and $v$ at $v$", ty := F ⟶ F ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real curvDom],
      doc := "the signed curvature `(x'y'' - y'x'')/(x'² + y'²)^{3/2}` at a regular point",
      value := close <| lamT F (fun _ => tt) fun x => lamT F (fun _ => tt) fun y =>
        lamT .real (fun t => curvDom x y t) fun t => curv x y t },
    curveAB phrase!"length of the curve with coordinates $v$ and $v$ on $[v,v]$" lengthIntegrand
      (fun x y a b => integral a b (lengthIntegrand x y)) "`∫_a^b √(x'² + y'²) dt`, for differentiable `x`, `y`",
    curveAB phrase!"signed area of the curve with coordinates $v$ and $v$ on $[v,v]$" areaIntegrand
      (fun x y a b => div (integral a b (areaIntegrand x y)) (num 2)) "`½ ∫_a^b (x y' - y x') dt` (Green)",
    { name := phrase!"curvature of the graph of $v$ at $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real twiceAt],
      doc := "`f''(x)/(1 + f'(x)²)^{3/2}`",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun x => twiceAt f x) fun x => graphCurv f x },
    { name := phrase!"radius of curvature of the graph of $v$ at $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun f x => and (twiceAt f x) (ne (d2 f x) (num 0))],
      doc := "`(1 + f'(x)²)^{3/2}/|f''(x)|`, where `f''(x) ≠ 0`",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun x => and (twiceAt f x) (ne (d2 f x) (num 0))) fun x =>
        div (threeHalves (add (num 1) (sq (deriv f x)))) (abs (d2 f x)) },
    polarAB phrase!"area enclosed by the polar curve $v$ on $[v,v]$" false polarArea
      (fun r a b => div (integral a b (polarArea r)) (num 2)) "`½ ∫_a^b r(θ)² dθ`",
    polarAB phrase!"length of the polar curve $v$ on $[v,v]$" true polarLen
      (fun r a b => integral a b (polarLen r)) "`∫_a^b √(r(θ)² + r'(θ)²) dθ`"]

end Leanify.Curves
