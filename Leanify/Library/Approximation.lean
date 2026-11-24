import Leanify.Library.Core

/-! # Vocabulary: numerical approximation

The formulas of a first course in numerical analysis that approximate a number, a
derivative, an integral or a function: errors and conditioning, rounding, difference
quotients, quadrature rules, and polynomial interpolation. The functions are real
functions on the line (`Let $f$ be a continuous function.`, with the field
`realfunctions`).

* notions of numbers: `absolute error of the approximation $\tilde x$ of $x$`, `relative
  error of the approximation $\tilde x$ of $x$` (`x ≠ 0`), `condition number of $f$ at $x$`
  (`|x f'(x)/f(x)|`), `rounding of $x$ to $k$ decimal places`, `machine epsilon of double
  precision` (`2^{-52}`), `unit roundoff of double precision` (`2^{-53}`);
* difference quotients of `f` at `x` with step `h ≠ 0`: forward, backward, central and
  second;
* quadrature on `[a,b]`, simple and composite with `n` subintervals: the trapezoidal rule,
  the midpoint rule, Simpson's rule (`n` even), the left and right Riemann sums;
* interpolation: the linear interpolant of `f` on `[a,b]`, the interpolation polynomial of
  degree `n` of `f` at equally spaced nodes on `[a,b]` (in Lagrange form), the `k`th
  Chebyshev node of order `n`.

Every meaning is a term of the core language (finite sums and products, the floor); a
quantity is defined where its formula is: a quotient where its denominator does not
vanish, a derivative where `f` is differentiable. -/

namespace Leanify.Approximation
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def exUnique (p : B → B) : B := exR fun m => and (p m) (allR fun m' => imp (p m') (eq m' m))
def derivAt (f x : B) : B := theR fun d => hasDeriv f x d
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def finProd (a b : B) (body : B → B) : B := app (app (app (prim .finProd) a) b) (lamR body)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posIntP (n : B) : B := and (isInt n) (lt (num 0) n)
def evenPosP (n : B) : B := and (posIntP n) (isInt (div n (num 2)))
def half : B := div (num 1) (num 2)
def pi : B := prim .pi
def cos (x : B) : B := app (prim (.realFn .cos)) x

/-- A quantity of `f` at `x` with step `h ≠ 0`. -/
def quot (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real, doc, doms := [none, none, dom1 .real fun h => ne h (num 0)],
    value := close <| lamT F (fun _ => tt) fun f => lamR fun x => lamT .real (fun h => ne h (num 0)) fun h => body f x h }
/-- A simple rule for `f` on `[a,b]`. -/
def rule (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real, doc,
    value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamR fun b => body f a b }
/-- A composite rule for `f` on `[a,b]` with `n` subintervals of length `h = (b-a)/n`,
`n` in the domain `d`. -/
def composite (name : Phrase) (d : B → B) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real ⟶ .real, doc, doms := [none, none, none, dom1 .real d],
    value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamR fun b => lamT .real d fun n =>
      body f a n (div (sub b a) n) }

/-- The nodes `a + k(b-a)/n`. -/
def node (a b n k : B) : B := add a (mul k (div (sub b a) n))
/-- `∑_k f(x_k) ∏_{j ≠ k} (x - x_j)/(x_k - x_j)`. -/
def lagrange (n f a b x : B) : B :=
  finSum (num 0) n fun k => mul (app f (node a b n k))
    (finProd (num 0) n fun j => cases (eq j k) (num 1)
      (div (sub x (node a b n j)) (sub (node a b n k) (node a b n j))))

def vocab : Vocab where
  notions := [
    { name := phrase!"absolute error of the approximation $v$ of $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`|x̃ - x|`", value := close <| lamR fun y => lamR fun x => abs (sub y x) },
    { name := phrase!"relative error of the approximation $v$ of $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real fun x => ne x (num 0)], doc := "`|x̃ - x|/|x|`, `x ≠ 0`",
      value := close <| lamR fun y => lamT .real (fun x => ne x (num 0)) fun x => div (abs (sub y x)) (abs x) },
    { name := phrase!"condition number of $v$ at $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun f x => and (exUnique fun d => hasDeriv f x d) (ne (app f x) (num 0))],
      doc := "`|x f'(x)/f(x)|`, where `f` is differentiable and `f(x) ≠ 0`",
      value := close <| lamT F (fun _ => tt) fun f =>
        lamT .real (fun x => and (exUnique fun d => hasDeriv f x d) (ne (app f x) (num 0))) fun x =>
          abs (div (mul x (derivAt f x)) (app f x)) },
    { name := phrase!"rounding of $v$ to $v$ decimal places", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real natP], doc := "`⌊10^k x + 1/2⌋/10^k` (to nearest, halves up)",
      value := close <| lamR fun x => lamT .real natP fun k =>
        div (floor (add (mul (zpow (num 10) k) x) half)) (zpow (num 10) k) },
    { name := phrase!"machine epsilon of double precision", ty := .real, doc := "`2^{-52}` (IEEE 754 binary64)",
      value := close <| zpow (num 2) (neg (num 52)) },
    { name := phrase!"unit roundoff of double precision", ty := .real, doc := "`2^{-53}` (IEEE 754 binary64)",
      value := close <| zpow (num 2) (neg (num 53)) },
    quot phrase!"forward difference quotient of $v$ at $v$ with step $v$"
      (fun f x h => div (sub (app f (add x h)) (app f x)) h) "`(f(x+h) - f(x))/h`, `h ≠ 0`",
    quot phrase!"backward difference quotient of $v$ at $v$ with step $v$"
      (fun f x h => div (sub (app f x) (app f (sub x h))) h) "`(f(x) - f(x-h))/h`, `h ≠ 0`",
    quot phrase!"central difference quotient of $v$ at $v$ with step $v$"
      (fun f x h => div (sub (app f (add x h)) (app f (sub x h))) (mul (num 2) h)) "`(f(x+h) - f(x-h))/(2h)`, `h ≠ 0`",
    quot phrase!"second difference quotient of $v$ at $v$ with step $v$"
      (fun f x h => div (add (sub (app f (add x h)) (mul (num 2) (app f x))) (app f (sub x h))) (mul h h))
      "`(f(x+h) - 2f(x) + f(x-h))/h²`, `h ≠ 0`",
    rule phrase!"trapezoidal rule for $v$ on $[v,v]$" (fun f a b => mul (div (sub b a) (num 2)) (add (app f a) (app f b)))
      "`(b-a)(f(a) + f(b))/2`",
    rule phrase!"midpoint rule for $v$ on $[v,v]$" (fun f a b => mul (sub b a) (app f (div (add a b) (num 2))))
      "`(b-a) f((a+b)/2)`",
    rule phrase!"Simpson's rule for $v$ on $[v,v]$"
      (fun f a b => mul (div (sub b a) (num 6)) (add (add (app f a) (mul (num 4) (app f (div (add a b) (num 2))))) (app f b)))
      "`(b-a)(f(a) + 4f((a+b)/2) + f(b))/6`",
    composite phrase!"trapezoidal rule for $v$ on $[v,v]$ with $v$ subintervals" posIntP
      (fun f a n h => mul h (add (div (add (app f a) (app f (add a (mul n h)))) (num 2))
        (finSum (num 1) (sub n (num 1)) fun k => app f (add a (mul k h)))))
      "`h (f(a)/2 + f(a+h) + … + f(b-h) + f(b)/2)`, `h = (b-a)/n`",
    composite phrase!"midpoint rule for $v$ on $[v,v]$ with $v$ subintervals" posIntP
      (fun f a n h => mul h (finSum (num 0) (sub n (num 1)) fun k => app f (add a (mul (add k half) h))))
      "`h ∑_{k<n} f(a + (k + 1/2)h)`",
    composite phrase!"Simpson's rule for $v$ on $[v,v]$ with $v$ subintervals" evenPosP
      (fun f a n h => mul (div h (num 3)) (finSum (num 0) n fun k =>
        mul (cases (or (eq k (num 0)) (eq k n)) (num 1) (cases (isInt (div k (num 2))) (num 2) (num 4))) (app f (add a (mul k h)))))
      "`(h/3)(f(x_0) + 4f(x_1) + 2f(x_2) + … + 4f(x_{n-1}) + f(x_n))`, `n` even",
    composite phrase!"left Riemann sum of $v$ on $[v,v]$ with $v$ subintervals" posIntP
      (fun f a n h => mul h (finSum (num 0) (sub n (num 1)) fun k => app f (add a (mul k h)))) "`h ∑_{k<n} f(a + kh)`",
    composite phrase!"right Riemann sum of $v$ on $[v,v]$ with $v$ subintervals" posIntP
      (fun f a n h => mul h (finSum (num 1) n fun k => app f (add a (mul k h)))) "`h ∑_{k=1}^{n} f(a + kh)`",
    { name := phrase!"linear interpolant of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ F,
      doms := [none, none, dom2 .real fun a b => lt a b],
      doc := "`x ↦ f(a) + (f(b) - f(a))(x - a)/(b - a)`, `a < b`",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamT .real (fun b => lt a b) fun b =>
        lamR fun x => add (app f a) (div (mul (sub (app f b) (app f a)) (sub x a)) (sub b a)) },
    { name := phrase!"interpolation polynomial of degree $v$ of $v$ at equally spaced nodes on $[v,v]$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ F,
      doms := [dom1 .real posIntP, none, none, dom2 .real fun a b => lt a b],
      doc := "the polynomial of degree `≤ n` equal to `f` at `a + k(b-a)/n`, `k = 0, …, n` (Lagrange form)",
      value := close <| lamT .real posIntP fun n => lamT F (fun _ => tt) fun f => lamR fun a =>
        lamT .real (fun b => lt a b) fun b => lamR fun x => lagrange n f a b x },
    { name := phrase!"$v$th Chebyshev node of order $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun k n => and (posIntP n) (lt k n)],
      doc := "`cos((2k+1)π/(2n))`, `0 ≤ k < n`",
      value := close <| lamT .real natP fun k => lamT .real (fun n => and (posIntP n) (lt k n)) fun n =>
        cos (div (mul (add (mul (num 2) k) (num 1)) pi) (mul (num 2) n)) }]

end Leanify.Approximation
