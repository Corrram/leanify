import Leanify.Library.Core

/-! # Vocabulary: quadratic and cubic polynomials by their coefficients

The classical quantities of `ax² + bx + c` (`a ≠ 0`) and of the depressed cubic `x³ + px + q`, by
their coefficients (`We write $D(a,b,c)$ for the discriminant of the quadratic with coefficients
$a$, $b$ and $c$.`). Polynomials as objects are in the field `polynomials`.

* notions: the discriminant `b² - 4ac`; the larger and the smaller real root (the greatest
  and the least real `x` with `ax² + bx + c = 0`, where there is one); the sum and the product
  of the roots (of the complex roots with multiplicity, Mathlib `Polynomial.roots`, where they
  are real); the vertex of the parabola (the `x` at which the quadratic takes its least or
  greatest value) and the extreme value (that value); the number of real roots (of elements of
  the set of the real roots); the discriminant `-4p³ - 27q²` of the cubic `x³ + px + q`, and its
  Cardano root `∛(-q/2 + √Δ') + ∛(-q/2 - √Δ')` (`Δ' = q²/4 + p³/27 ≥ 0`).

The closed forms (`(-b ± √(b² - 4ac))/(2a)`, Vieta's `-b/a` and `c/a`, `-b/(2a)`,
`c - b²/(4a)`, the count by the sign of the discriminant) are theorems, not definitions. The
sum and the product of the roots are constants, interpreted by the declarations of
`Leanify/Library/QuadraticsModel.lean`; the other meanings are terms of the core language. -/

namespace Leanify.Quadratics
open Build Core

def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def cbrt (x : B) : B := mul (cases (lt x (num 0)) (neg (num 1)) (num 1)) (app2 (prim .rpow) (abs x) (div (num 1) (num 3)))
def disc (a b c : B) : B := sub (mul b b) (mul (num 4) (mul a c))
def nz (a : B) : B := ne a (num 0)
def quad (name : Phrase) (d : B → B → B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real nz, none, dom3 .real d], doc,
    value := close <| lamT .real nz fun a => lamR fun b => lamT .real (fun c => d a b c) fun c => body a b c }
def any3 (_ _ _ : B) : B := tt
/-- `x` is a real root of `ax² + bx + c`. -/
def root (a b c x : B) : B := eq (add (add (mul a (mul x x)) (mul b x)) c) (num 0)
def hasRoot (a b c : B) : B := exR fun x => root a b c x
/-- The value of the quadratic at `x`. -/
def val (a b c x : B) : B := add (add (mul a (mul x x)) (mul b x)) c
/-- `x` is where the quadratic takes its least or its greatest value. -/
def extremeAt (a b c x : B) : B :=
  or (allR fun y => le (val a b c x) (val a b c y)) (allR fun y => le (val a b c y) (val a b c x))
def app3 (f x y z : B) : B := app (app2 f x y) z

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def rootSum : Nat := 0
def rootProd : Nat := 1
def rootSumReal : Nat := 2
def rootProdReal : Nat := 3
end Const
def cubicD (p q : B) : B := add (div (mul q q) (num 4)) (div (mul p (mul p p)) (num 27))

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .prop,
    .real ⟶ .real ⟶ .real ⟶ .prop]
  constNames := [w!"\\Sigma_{#1,#2,#3}", w!"\\Pi_{#1,#2,#3}", w!"\\Sigma_{#1,#2,#3}\\in\\mathbb{R}", w!"\\Pi_{#1,#2,#3}\\in\\mathbb{R}"]
  constLean := [w!"Leanify.Quadratics.rootSum", w!"Leanify.Quadratics.rootProd", w!"Leanify.Quadratics.RootSumReal",
    w!"Leanify.Quadratics.RootProdReal"]
  modules := [w!"Leanify.Library.QuadraticsModel"]
  notions := [
    { name := phrase!"discriminant of the quadratic with coefficients $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`b² - 4ac`", value := close <| lamR fun a => lamR fun b => lamR fun c => disc a b c },
    quad phrase!"larger root of the quadratic with coefficients $v$, $v$ and $v$" hasRoot
      (fun a b c => theR fun x => and (root a b c x) (allR fun y => imp (root a b c y) (le y x)))
      "the greatest real `x` with `ax² + bx + c = 0`, where there is one (`(-b + √(b² - 4ac))/(2a)` for `a > 0`)",
    quad phrase!"smaller root of the quadratic with coefficients $v$, $v$ and $v$" hasRoot
      (fun a b c => theR fun x => and (root a b c x) (allR fun y => imp (root a b c y) (le x y)))
      "the least real `x` with `ax² + bx + c = 0`, where there is one (`(-b - √(b² - 4ac))/(2a)` for `a > 0`)",
    quad phrase!"sum of the roots of the quadratic with coefficients $v$, $v$ and $v$"
      (fun a b c => app3 (const Const.rootSumReal) a b c) (fun a b c => app3 (const Const.rootSum) a b c)
      "the sum of the complex roots with multiplicity, a real number (`-b/a`, Vieta)",
    quad phrase!"product of the roots of the quadratic with coefficients $v$, $v$ and $v$"
      (fun a b c => app3 (const Const.rootProdReal) a b c) (fun a b c => app3 (const Const.rootProd) a b c)
      "the product of the complex roots with multiplicity, a real number (`c/a`, Vieta)",
    quad phrase!"vertex of the parabola with coefficients $v$, $v$ and $v$" any3 (fun a b c => theR fun x => extremeAt a b c x)
      "the `x` at which `ax² + bx + c` takes its least or its greatest value (`-b/(2a)`)",
    quad phrase!"extreme value of the quadratic with coefficients $v$, $v$ and $v$" any3
      (fun a b c => theR fun v => exR fun x => and (eq (val a b c x) v) (extremeAt a b c x))
      "the least value of `ax² + bx + c` for `a > 0`, the greatest for `a < 0` (`c - b²/(4a)`)",
    quad phrase!"number of real roots of the quadratic with coefficients $v$, $v$ and $v$" any3
      (fun a b c => theR fun r => app2 (prim .cardIs) (lamR fun x => root a b c x) r)
      "the number of elements of the set of the real `x` with `ax² + bx + c = 0` (`2`, `1` or `0` by the sign of `b² - 4ac`)",
    { name := phrase!"discriminant of the cubic with coefficients $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`-4p³ - 27q²` for `x³ + px + q`",
      value := close <| lamR fun p => lamR fun q => sub (neg (mul (num 4) (mul p (mul p p)))) (mul (num 27) (mul q q)) },
    { name := phrase!"Cardano root of the cubic with coefficients $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun p q => le (num 0) (cubicD p q)],
      doc := "`∛(-q/2 + √Δ') + ∛(-q/2 - √Δ')`, `Δ' = q²/4 + p³/27 ≥ 0`: the real root of `x³ + px + q`",
      value := close <| lamR fun p => lamT .real (fun q => le (num 0) (cubicD p q)) fun q =>
        add (cbrt (add (neg (div q (num 2))) (sqrt (cubicD p q)))) (cbrt (sub (neg (div q (num 2))) (sqrt (cubicD p q)))) }]

end Leanify.Quadratics
