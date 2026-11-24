import Leanify.Library.Core

/-! # Vocabulary: ordinary differential equations and one-step methods

The scalar initial value problem `y'(t) = f(t, y(t))`, `y(t_0) = y_0`, for a right-hand
side `f` that is a real function of two real variables (`Let $f:\mathbb{R}^2\to\mathbb{R}$
be a continuous function.`, or a variable bound by the noun `right-hand side`), and the
one-step methods that approximate its solutions.

* nouns: `right-hand side` (a real function of `t` and `y`);
* adjectives of right-hand sides: `Lipschitz in the second variable`, `Lipschitz in the
  second variable with constant $L$` (`|f(t,y) - f(t,z)| ≤ L|y - z|`);
* adjectives of real functions `y`, with the right-hand side: `solution of the differential
  equation with right-hand side $f$`, `solution of the initial value problem with
  right-hand side $f$ and initial value $y_0$ at $t_0$`;
* notions: the explicit Euler, Heun, explicit midpoint and classical Runge–Kutta steps of
  `f` with step size `h` (each a function `(t, y) ↦ y_{new}`);
* adjectives of sequences: `Euler sequence for $f$ with step size $h$` and `Runge-Kutta
  sequence for $f$ with step size $h$` (`y_{n+1}` is the step from `(nh, y_n)`);
* adjectives of real functions: `solution of the linear equation with constant coefficients
  $a$ and $b$` (`y'' + a y' + b y = 0`), the same `and forcing $h$` (`= h`), `solution of
  the logistic equation with rate $r$ and capacity $K$`.

Every meaning is a term of the core language. A solution is differentiable everywhere,
with the derivative the equation prescribes. -/

namespace Leanify.OdeSolvers
open Build Core

abbrev F : Ty := Ty.rfun
/-- Right-hand sides: real functions of `t` and `y`. -/
abbrev R : Ty := .real ⟶ .real ⟶ .real

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def f2 (f t y : B) : B := app2 f t y
def half (x : B) : B := div x (num 2)

def euler (f h t y : B) : B := add y (mul h (f2 f t y))
def heun (f h t y : B) : B :=
  add y (mul (half h) (add (f2 f t y) (f2 f (add t h) (add y (mul h (f2 f t y))))))
def midpoint (f h t y : B) : B :=
  add y (mul h (f2 f (add t (half h)) (add y (mul (half h) (f2 f t y)))))
def rk4 (f h t y : B) : B :=
  let k1 := f2 f t y
  let k2 := f2 f (add t (half h)) (add y (mul (half h) k1))
  let k3 := f2 f (add t (half h)) (add y (mul (half h) k2))
  let k4 := f2 f (add t h) (add y (mul h k3))
  add y (mul (div h (num 6)) (add (add k1 (mul (num 2) k2)) (add (mul (num 2) k3) k4)))
def lipschitzY (f l : B) : B := allR fun t => allR fun y => allR fun z => le (abs (sub (f2 f t y) (f2 f t z))) (mul l (abs (sub y z)))
def solves (f y : B) : B := allR fun t => hasDeriv y t (f2 f t (app y t))
def forNat (body : B → B) : B := allR fun n => imp (isNat n) (body n)
/-- `y'' + a y' + b y = h`, with `y'` the function `g`. -/
def second (a b h y : B) : B :=
  exT F fun g => and (allR fun t => hasDeriv y t (app g t))
    (allR fun t => hasDeriv g t (sub (sub (app h t) (mul a (app g t))) (mul b (app y t))))

def step (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := R ⟶ .real ⟶ R, doc,
    value := close <| lamT R (fun _ => tt) fun f => lamR fun h => lamR fun t => lamR fun y => body f h t y }
def seqWith (p : Phrase) (body : B → B → B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamT R (fun _ => tt) fun f => lamR fun h => lamT F (fun _ => tt) fun a =>
      forNat fun n => eq (app a (add n (num 1))) (body f h (mul n h) (app a n)) }

def vocab : Vocab where
  nouns := [
    { sing := phrase!"right-hand side", plural := phrase!"right-hand sides", ty := R,
      pred := close <| lamT R (fun _ => tt) fun _ => tt, doc := "a real function `f(t, y)` of two real variables" }]
  mods := [
    { phrase := phrase!"Lipschitz in the second variable", prenominal := false, ty := R,
      pred := close <| lamT R (fun _ => tt) fun f => exR fun l => lipschitzY f l,
      doc := "`|f(t,y) - f(t,z)| ≤ L|y - z|` for some `L`" },
    { phrase := phrase!"Lipschitz in the second variable with constant $v$", prenominal := false, ty := R,
      pred := close <| lamR fun l => lamT R (fun _ => tt) fun f => lipschitzY f l,
      doc := "`|f(t,y) - f(t,z)| ≤ L|y - z|`" },
    { phrase := phrase!"solution of the differential equation with right-hand side $v$", prenominal := false, ty := F,
      pred := close <| lamT R (fun _ => tt) fun f => lamT F (fun _ => tt) fun y => solves f y,
      doc := "`y'(t) = f(t, y(t))` for every `t` (Mathlib `HasDerivAt`)" },
    { phrase := phrase!"solution of the initial value problem with right-hand side $v$ and initial value $v$ at $v$",
      prenominal := false, ty := F,
      pred := close <| lamT R (fun _ => tt) fun f => lamR fun y0 => lamR fun t0 => lamT F (fun _ => tt) fun y =>
        and (solves f y) (eq (app y t0) y0),
      doc := "`y'(t) = f(t, y(t))` for every `t` and `y(t_0) = y_0`" },
    { phrase := phrase!"solution of the linear equation with constant coefficients $v$ and $v$", prenominal := false, ty := F,
      pred := close <| lamR fun a => lamR fun b => lamT F (fun _ => tt) fun y => second a b (lamR fun _ => num 0) y,
      doc := "`y'' + a y' + b y = 0`: `y` and `y'` differentiable everywhere" },
    { phrase := phrase!"solution of the linear equation with constant coefficients $v$ and $v$ and forcing $v$", prenominal := false, ty := F,
      pred := close <| lamR fun a => lamR fun b => lamT F (fun _ => tt) fun h => lamT F (fun _ => tt) fun y => second a b h y,
      doc := "`y'' + a y' + b y = h`" },
    { phrase := phrase!"solution of the logistic equation with rate $v$ and capacity $v$", prenominal := false, ty := F,
      pred := close <| lamR fun r => lamR fun k => lamT F (fun _ => tt) fun y =>
        allR fun t => hasDeriv y t (mul (mul r (app y t)) (sub (num 1) (div (app y t) k))),
      doc := "`y' = r y (1 - y/K)`" },
    seqWith phrase!"Euler sequence for $v$ with step size $v$" euler "`y_{n+1} = y_n + h f(nh, y_n)`",
    seqWith phrase!"Runge-Kutta sequence for $v$ with step size $v$" rk4 "`y_{n+1}` is the classical Runge–Kutta step from `(nh, y_n)`"]
  notions := [
    step phrase!"Euler step of $v$ with step size $v$" euler "`(t, y) ↦ y + h f(t, y)` (explicit Euler)",
    step phrase!"Heun step of $v$ with step size $v$" heun "`(t, y) ↦ y + (h/2)(f(t,y) + f(t+h, y + h f(t,y)))`",
    step phrase!"midpoint step of $v$ with step size $v$" midpoint "`(t, y) ↦ y + h f(t + h/2, y + (h/2) f(t,y))`",
    step phrase!"Runge-Kutta step of $v$ with step size $v$" rk4 "the classical fourth-order Runge–Kutta step"]

end Leanify.OdeSolvers
