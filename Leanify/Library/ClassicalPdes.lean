import Leanify.Library.Core

/-! # Vocabulary: classical partial differential equations in one space dimension

Solutions `u(x,t)` (or `u(x,y)`) of the heat, wave, transport, Laplace and Burgers equations,
a real function of two variables (`Let $u:\mathbb{R}^2\to\mathbb{R}$ be a function.`), with the
heat kernel and d'Alembert's formula: `$u$ is a solution of the heat equation with
diffusivity $k$`.

* adjectives of functions of two variables: `solution of the heat equation with diffusivity
  $k$` (`u_t = k u_{xx}`), `solution of the wave equation with speed $c$` (`u_{tt} = c² u_{xx}`),
  `solution of the transport equation with speed $c$` (`u_t + c u_x = 0`), `harmonic` and
  `solution of Laplace's equation` (`u_{xx} + u_{yy} = 0`), `solution of Burgers' equation with
  viscosity $\nu$` (`u_t + u u_x = ν u_{xx}`), each with the partial derivatives existing
  everywhere;
* notions: the partial derivatives `u_x`, `u_t` at a point, the heat kernel with diffusivity
  `k` (`e^{-x²/(4kt)}/√(4πkt)` for `t > 0`), d'Alembert's solution with speed `c`, initial
  displacement `f` and initial velocity `g`.

Partial derivatives are descriptions; every meaning is a term of the core language. -/

namespace Leanify.ClassicalPdes
open Build Core

abbrev F : Ty := Ty.rfun
abbrev F2 : Ty := .real ⟶ .real ⟶ .real

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def inX (u t : B) : B := lamR fun s => app2 u s t
def inT (u x : B) : B := lamR fun s => app2 u x s
/-- `u_x` and `u_t` (the second variable), as functions of two variables. -/
def px (u : B) : B := lamR fun x => lamR fun t => deriv (inX u t) x
def pt (u : B) : B := lamR fun x => lamR fun t => deriv (inT u x) t
def diffX (u : B) : B := allR fun x => allR fun t => diffAt (inX u t) x
def diffT (u : B) : B := allR fun x => allR fun t => diffAt (inT u x) t
def at2 (u x t : B) : B := app2 u x t
def everywhere (body : B → B → B) : B := allR fun x => allR fun t => body x t
def exp (x : B) : B := app (prim (.realFn .exp)) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def pi : B := prim .pi
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def any (_ : B) : B := tt
def eqn (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F2, doc,
    pred := close <| lamR fun k => lamT F2 any fun u => body k u }
def second (u : B) : B := and (diffX u) (diffX (px u))

def vocab : Vocab where
  mods := [
    eqn phrase!"solution of the heat equation with diffusivity $v$"
      (fun k u => and (second u) (and (diffT u) (everywhere fun x t => eq (at2 (pt u) x t) (mul k (at2 (px (px u)) x t)))))
      "`u_t = k u_{xx}` everywhere",
    eqn phrase!"solution of the wave equation with speed $v$"
      (fun c u => and (second u) (and (and (diffT u) (diffT (pt u)))
        (everywhere fun x t => eq (at2 (pt (pt u)) x t) (mul (mul c c) (at2 (px (px u)) x t)))))
      "`u_{tt} = c² u_{xx}` everywhere",
    eqn phrase!"solution of the transport equation with speed $v$"
      (fun c u => and (diffX u) (and (diffT u) (everywhere fun x t => eq (add (at2 (pt u) x t) (mul c (at2 (px u) x t))) (num 0))))
      "`u_t + c u_x = 0` everywhere",
    eqn phrase!"solution of Burgers' equation with viscosity $v$"
      (fun n u => and (second u) (and (diffT u)
        (everywhere fun x t => eq (add (at2 (pt u) x t) (mul (at2 u x t) (at2 (px u) x t))) (mul n (at2 (px (px u)) x t)))))
      "`u_t + u u_x = ν u_{xx}` everywhere",
    { phrase := phrase!"harmonic", prenominal := true, ty := F2,
      pred := close <| lamT F2 any fun u => and (second u) (and (and (diffT u) (diffT (pt u)))
        (everywhere fun x y => eq (add (at2 (px (px u)) x y) (at2 (pt (pt u)) x y)) (num 0))),
      doc := "`u_{xx} + u_{yy} = 0` everywhere" },
    { phrase := phrase!"solution of Laplace's equation", prenominal := false, ty := F2,
      pred := close <| lamT F2 any fun u => and (second u) (and (and (diffT u) (diffT (pt u)))
        (everywhere fun x y => eq (add (at2 (px (px u)) x y) (at2 (pt (pt u)) x y)) (num 0))),
      doc := "`u_{xx} + u_{yy} = 0` everywhere" }]
  notions := [
    { name := phrase!"partial derivative of $v$ in the first variable at $v$ and $v$", ty := F2 ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun u x t => diffAt (inX u t) x],
      doc := "`∂u/∂x (x,t)`, where it exists",
      value := close <| lamT F2 any fun u => lamR fun x => lamT .real (fun t => diffAt (inX u t) x) fun t => deriv (inX u t) x },
    { name := phrase!"partial derivative of $v$ in the second variable at $v$ and $v$", ty := F2 ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun u x t => diffAt (inT u x) t],
      doc := "`∂u/∂t (x,t)`, where it exists",
      value := close <| lamT F2 any fun u => lamR fun x => lamT .real (fun t => diffAt (inT u x) t) fun t => deriv (inT u x) t },
    { name := phrase!"heat kernel with diffusivity $v$", ty := .real ⟶ F2, doms := [dom1 .real fun k => lt (num 0) k],
      doc := "`(x,t) ↦ e^{-x²/(4kt)}/√(4πkt)` for `t > 0` (and `0` for `t ≤ 0`)",
      value := close <| lamT .real (fun k => lt (num 0) k) fun k => lamR fun x => lamR fun t =>
        cases (lt (num 0) t) (div (exp (neg (div (mul x x) (mul (mul (num 4) k) t)))) (sqrt (mul (mul (mul (num 4) pi) k) t))) (num 0) },
    { name := phrase!"d'Alembert solution with speed $v$, initial displacement $v$ and initial velocity $v$",
      ty := .real ⟶ F ⟶ F ⟶ F2, doms := [dom1 .real fun c => lt (num 0) c, none, none],
      doc := "`(x,t) ↦ (f(x-ct) + f(x+ct))/2 + (1/(2c)) ∫_{x-ct}^{x+ct} g`",
      value := close <| lamT .real (fun c => lt (num 0) c) fun c => lamT F any fun f => lamT F any fun g => lamR fun x => lamR fun t =>
        add (div (add (app f (sub x (mul c t))) (app f (add x (mul c t)))) (num 2))
          (div (integral (sub x (mul c t)) (add x (mul c t)) g) (mul (num 2) c)) }]

end Leanify.ClassicalPdes
