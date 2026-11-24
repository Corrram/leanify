import Leanify.Library.Core

/-! # Vocabulary: descent methods

Line searches and descent iterations for a differentiable real function `f` on the line,
as in the analysis of gradient methods (`$t$ is an Armijo step for $f$ at $x$ in direction
$d$ with constant $c$`).

* adjectives of a step size `t > 0`, with `f`, the point `x`, the direction `d` and the
  constants: `Armijo step for $f$ at $x$ in direction $d$ with constant $c$`
  (`f(x + td) ≤ f(x) + c t f'(x) d`), `Wolfe step for $f$ at $x$ in direction $d$ with
  constants $c_1$ and $c_2$` (with the curvature condition `f'(x + td) d ≥ c₂ f'(x) d`);
* adjectives of a direction: `descent direction for $f$ at $x$` (`f'(x) d < 0`);
* adjectives of sequences: `gradient descent sequence for $f$ with step size $h$`
  (`x_{n+1} = x_n - h f'(x_n)`), `heavy-ball sequence for $f$ with step size $h$ and
  momentum $\beta$` (`x_{n+2} = x_{n+1} - h f'(x_{n+1}) + β(x_{n+1} - x_n)`), `proximal point
  sequence for $f$ with parameter $\lambda$` (`x_{n+1}` minimizes `f(z) + (z - x_n)²/(2λ)`).

`f'` is the derivative where it exists (a description); every meaning is a term of the core
language. -/

namespace Leanify.Descent
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def nat (n : B) : B := and (isInt n) (le (num 0) n)
def forNat (body : B → B) : B := allR fun n => imp (nat n) (body n)
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def differentiable (f : B) : B := allR fun x => diffAt f x
def armijo (f x d c t : B) : B :=
  and (lt (num 0) t) (le (app f (add x (mul t d))) (add (app f x) (mul (mul c t) (mul (deriv f x) d))))
def curvature (f x d c t : B) : B := le (mul c (mul (deriv f x) d)) (mul (deriv f (add x (mul t d))) d)
def isMinOf (g z : B) : B := allR fun w => le (app g z) (app g w)

def vocab : Vocab where
  mods := [
    { phrase := phrase!"Armijo step for $v$ at $v$ in direction $v$ with constant $v$", prenominal := false, ty := .real,
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun x => lamR fun d => lamR fun c => lamR fun t =>
        and (differentiable f) (armijo f x d c t),
      doc := "`t > 0` and `f(x + td) ≤ f(x) + c t f'(x) d`, for a differentiable `f`" },
    { phrase := phrase!"Wolfe step for $v$ at $v$ in direction $v$ with constants $v$ and $v$", prenominal := false, ty := .real,
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun x => lamR fun d => lamR fun c1 => lamR fun c2 => lamR fun t =>
        and (differentiable f) (and (armijo f x d c1 t) (curvature f x d c2 t)),
      doc := "the Armijo condition with `c₁` and `f'(x + td) d ≥ c₂ f'(x) d`" },
    { phrase := phrase!"descent direction for $v$ at $v$", prenominal := false, ty := .real,
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun x => lamR fun d => and (diffAt f x) (lt (mul (deriv f x) d) (num 0)),
      doc := "`f'(x) d < 0`" },
    { phrase := phrase!"gradient descent sequence for $v$ with step size $v$", prenominal := false, ty := F,
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun h => lamT F (fun _ => tt) fun a =>
        and (differentiable f) (forNat fun n => eq (app a (add n (num 1))) (sub (app a n) (mul h (deriv f (app a n))))),
      doc := "`x_{n+1} = x_n - h f'(x_n)`, for a differentiable `f`" },
    { phrase := phrase!"heavy-ball sequence for $v$ with step size $v$ and momentum $v$", prenominal := false, ty := F,
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun h => lamR fun b => lamT F (fun _ => tt) fun a =>
        and (differentiable f) (forNat fun n => eq (app a (add n (num 2)))
          (add (sub (app a (add n (num 1))) (mul h (deriv f (app a (add n (num 1)))))) (mul b (sub (app a (add n (num 1))) (app a n))))),
      doc := "`x_{n+2} = x_{n+1} - h f'(x_{n+1}) + β(x_{n+1} - x_n)` (Polyak)" },
    { phrase := phrase!"proximal point sequence for $v$ with parameter $v$", prenominal := false, ty := F,
      pred := close <| lamT F (fun _ => tt) fun f => lamR fun l => lamT F (fun _ => tt) fun a =>
        and (lt (num 0) l) (forNat fun n => isMinOf (lamR fun z => add (app f z) (div (mul (sub z (app a n)) (sub z (app a n))) (mul (num 2) l)))
          (app a (add n (num 1)))),
      doc := "`x_{n+1}` minimizes `f(z) + (z - x_n)²/(2λ)`, `λ > 0`" }]

end Leanify.Descent
