import Leanify.Library.Core

/-! # Vocabulary: quadratic and cubic polynomials by their coefficients

The classical quantities of `ax² + bx + c` (`a ≠ 0`) and of the depressed cubic `x³ + px + q`, by
their coefficients (`We write $D(a,b,c)$ for the discriminant of the quadratic with coefficients
$a$, $b$ and $c$.`). Polynomials as objects are in the field `polynomials`.

* notions: the discriminant `b² - 4ac`; the larger and the smaller real root
  `(-b ± √(b² - 4ac))/(2a)` (where the discriminant is nonnegative, for `a > 0`); the sum `-b/a`
  and the product `c/a` of the roots; the vertex `-b/(2a)` and the extreme value
  `c - b²/(4a)`; the number of real roots (`2`, `1` or `0`); the discriminant `-4p³ - 27q²` of the
  cubic `x³ + px + q`, and its real root `∛(-q/2 + √Δ') + ∛(-q/2 - √Δ')` (Cardano, `Δ' = q²/4 + p³/27 ≥ 0`).

Every meaning is a term of the core language. -/

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
def realRoots (a b c : B) : B := and (lt (num 0) a) (le (num 0) (disc a b c))
def cubicD (p q : B) : B := add (div (mul q q) (num 4)) (div (mul p (mul p p)) (num 27))

def vocab : Vocab where
  notions := [
    { name := phrase!"discriminant of the quadratic with coefficients $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`b² - 4ac`", value := close <| lamR fun a => lamR fun b => lamR fun c => disc a b c },
    quad phrase!"larger root of the quadratic with coefficients $v$, $v$ and $v$" realRoots
      (fun a b c => div (add (neg b) (sqrt (disc a b c))) (mul (num 2) a)) "`(-b + √(b² - 4ac))/(2a)`, for `a > 0` and `b² ≥ 4ac`",
    quad phrase!"smaller root of the quadratic with coefficients $v$, $v$ and $v$" realRoots
      (fun a b c => div (sub (neg b) (sqrt (disc a b c))) (mul (num 2) a)) "`(-b - √(b² - 4ac))/(2a)`, for `a > 0` and `b² ≥ 4ac`",
    quad phrase!"sum of the roots of the quadratic with coefficients $v$, $v$ and $v$" any3 (fun a b _ => neg (div b a)) "`-b/a` (Vieta)",
    quad phrase!"product of the roots of the quadratic with coefficients $v$, $v$ and $v$" any3 (fun a _ c => div c a) "`c/a` (Vieta)",
    quad phrase!"vertex of the parabola with coefficients $v$, $v$ and $v$" any3 (fun a b _ => neg (div b (mul (num 2) a))) "`-b/(2a)`",
    quad phrase!"extreme value of the quadratic with coefficients $v$, $v$ and $v$" any3
      (fun a b c => sub c (div (mul b b) (mul (num 4) a))) "`c - b²/(4a)`, the minimum for `a > 0`, the maximum for `a < 0`",
    quad phrase!"number of real roots of the quadratic with coefficients $v$, $v$ and $v$" any3
      (fun a b c => cases (lt (num 0) (disc a b c)) (num 2) (cases (eq (disc a b c) (num 0)) (num 1) (num 0))) "`2`, `1` or `0` by the sign of `b² - 4ac`",
    { name := phrase!"discriminant of the cubic with coefficients $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`-4p³ - 27q²` for `x³ + px + q`",
      value := close <| lamR fun p => lamR fun q => sub (neg (mul (num 4) (mul p (mul p p)))) (mul (num 27) (mul q q)) },
    { name := phrase!"Cardano root of the cubic with coefficients $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun p q => le (num 0) (cubicD p q)],
      doc := "`∛(-q/2 + √Δ') + ∛(-q/2 - √Δ')`, `Δ' = q²/4 + p³/27 ≥ 0`: the real root of `x³ + px + q`",
      value := close <| lamR fun p => lamT .real (fun q => le (num 0) (cubicD p q)) fun q =>
        add (cbrt (add (neg (div q (num 2))) (sqrt (cubicD p q)))) (cbrt (sub (neg (div q (num 2))) (sqrt (cubicD p q)))) }]

end Leanify.Quadratics
