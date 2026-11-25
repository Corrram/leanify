import Leanify.Library.Core

/-! # Vocabulary: calculus of variations

Functionals of a function `y` on `[a,b]` given by a Lagrangian `L(t, y, p)`, a real function of
three variables (`Let $L:\mathbb{R}^3\to\mathbb{R}$ be a function.`), and their extremals:
`$y$ is a solution of the Euler-Lagrange equation for $L$ on $[a,b]$`.

* notions: the action `∫_a^b L(t, y(t), y'(t)) dt` of `y` (where `y` is differentiable and the
  integrand integrable), the arc-length functional `∫_a^b √(1 + y'²)` and the Dirichlet energy
  `½ ∫_a^b y'²`, the Hamiltonian `p L_p - L` at a point;
* adjectives of functions: `solution of the Euler-Lagrange equation for $L$ on $[a,b]$`
  (`d/dt L_p(t, y, y') = L_y(t, y, y')` on `[a,b]`, with the partial derivatives existing),
  `minimizer of the action of $L$ on $[a,b]$ with the same endpoint values` (no function with
  the values of `y` at `a` and `b` has a smaller action), `extremal with fixed endpoints $\alpha$
  and $\beta$ on $[a,b]$` (`y(a) = α`, `y(b) = β`).

Partial and ordinary derivatives are descriptions; every meaning is a term of the core
language. -/

namespace Leanify.Variations
open Build Core

abbrev F : Ty := Ty.rfun
abbrev F3 : Ty := .real ⟶ .real ⟶ .real ⟶ .real

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def diff (f : B) : B := allR fun x => diffAt f x
def app3 (f a b c : B) : B := app (app2 f a b) c
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def integrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def inI (a b t : B) : B := and (le a t) (le t b)
/-- `L_y(t, y, p)` and `L_p(t, y, p)`. -/
def lY (l t y p : B) : B := deriv (lamR fun s => app3 l t s p) y
def lP (l t y p : B) : B := deriv (lamR fun s => app3 l t y s) p
def lagr (l y : B) : B := lamR fun t => app3 l t (app y t) (deriv y t)
def action (l y a b : B) : B := integral a b (lagr l y)
def actionDom (l y a b : B) : B := and (le a b) (and (diff y) (integrable (lagr l y) a b))
def any (_ : B) : B := tt

def vocab : Vocab where
  mods := [
    { phrase := phrase!"solution of the Euler-Lagrange equation for $v$ on $[v,v]$", prenominal := false, ty := F,
      pred := close <| lamT F3 any fun l => lamR fun a => lamR fun b => lamT F any fun y =>
        and (diff y) (allR fun t => imp (inI a b t)
          (hasDeriv (lamR fun s => lP l s (app y s) (deriv y s)) t (lY l t (app y t) (deriv y t)))),
      doc := "`d/dt L_p(t, y, y') = L_y(t, y, y')` on `[a,b]`" },
    { phrase := phrase!"minimizer of the action of $v$ on $[v,v]$ with the same endpoint values", prenominal := false, ty := F,
      pred := close <| lamT F3 any fun l => lamR fun a => lamR fun b => lamT F any fun y =>
        and (actionDom l y a b) (allT F fun z => imp (and (actionDom l z a b) (and (eq (app z a) (app y a)) (eq (app z b) (app y b))))
          (le (action l y a b) (action l z a b))),
      doc := "no differentiable `z` with `z(a) = y(a)`, `z(b) = y(b)` has a smaller action" },
    { phrase := phrase!"function with endpoint values $v$ and $v$ on $[v,v]$", prenominal := false, ty := F,
      pred := close <| lamR fun al => lamR fun be => lamR fun a => lamR fun b => lamT F any fun y =>
        and (eq (app y a) al) (eq (app y b) be),
      doc := "`y(a) = α`, `y(b) = β`" }]
  notions := [
    { name := phrase!"action of $v$ under $v$ on $[v,v]$", ty := F ⟶ F3 ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, none, dom4 .real fun y l a b => actionDom l y a b],
      doc := "`∫_a^b L(t, y(t), y'(t)) dt`",
      value := close <| lamT F any fun y => lamT F3 any fun l => lamR fun a => lamT .real (fun b => actionDom l y a b) fun b => action l y a b },
    { name := phrase!"arc-length functional of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun y a b => and (le a b) (and (diff y) (integrable (lamR fun t => sqrt (add (num 1) (mul (deriv y t) (deriv y t)))) a b))],
      doc := "`∫_a^b √(1 + y'²)`",
      value := close <| lamT F any fun y => lamR fun a =>
        lamT .real (fun b => and (le a b) (and (diff y) (integrable (lamR fun t => sqrt (add (num 1) (mul (deriv y t) (deriv y t)))) a b))) fun b =>
          integral a b (lamR fun t => sqrt (add (num 1) (mul (deriv y t) (deriv y t)))) },
    { name := phrase!"Dirichlet energy of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun y a b => and (le a b) (and (diff y) (integrable (lamR fun t => mul (deriv y t) (deriv y t)) a b))],
      doc := "`½ ∫_a^b y'²`",
      value := close <| lamT F any fun y => lamR fun a =>
        lamT .real (fun b => and (le a b) (and (diff y) (integrable (lamR fun t => mul (deriv y t) (deriv y t)) a b))) fun b =>
          div (integral a b (lamR fun t => mul (deriv y t) (deriv y t))) (num 2) },
    { name := phrase!"Hamiltonian of $v$ at $v$, $v$ and $v$", ty := F3 ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, none, dom4 .real fun l t y p => diffAt (lamR fun s => app3 l t y s) p],
      doc := "`p L_p(t, y, p) - L(t, y, p)`",
      value := close <| lamT F3 any fun l => lamR fun t => lamR fun y => lamT .real (fun p => diffAt (lamR fun s => app3 l t y s) p) fun p =>
        sub (mul p (lP l t y p)) (app3 l t y p) }]

end Leanify.Variations
