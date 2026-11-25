import Leanify.Library.Core

/-! # Vocabulary: integral equations

Linear integral equations of the second kind and Abel's equation, for a kernel `K`, a real
function of two variables (`Let $K:\mathbb{R}^2\to\mathbb{R}$ be a function.`), and a right-hand
side `g`: `$y$ is a solution of the Volterra integral equation with kernel $K$ and right-hand
side $g$ from $a$`.

* adjectives of functions: `solution of the Volterra integral equation with kernel $K$ and
  right-hand side $g$ from $a$` (`y(x) = g(x) + ∫_a^x K(x,t) y(t) dt` for `x ≥ a`), `solution of
  the Fredholm integral equation with kernel $K$, right-hand side $g$ and parameter $\lambda$ on
  $[a,b]$` (`y(x) = g(x) + λ ∫_a^b K(x,t) y(t) dt` for `x ∈ [a,b]`), `solution of the homogeneous
  Fredholm integral equation with kernel $K$ and parameter $\lambda$ on $[a,b]$`, `solution of
  Abel's integral equation with right-hand side $g$ from $a$` (`∫_a^x y(t)/√(x-t) dt = g(x)`
  for `x > a`);
* adjectives of kernels: `symmetric kernel` (`K(x,t) = K(t,x)`), `kernel of Volterra type`
  (`K(x,t) = 0` for `t > x`);
* notions: the second iterated kernel on `[a,b]` (`∫_a^b K(x,s) K(s,t) ds`), the value at `x`
  of the integral operator with kernel `K` on `[a,b]` applied to `y`.

Every meaning is a term of the core language. -/

namespace Leanify.IntegralEquations
open Build Core

abbrev F : Ty := Ty.rfun
abbrev F2 : Ty := .real ⟶ .real ⟶ .real

def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def integrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def inI (a b x : B) : B := and (le a x) (le x b)
def kernelTimes (k y x : B) : B := lamR fun t => mul (app2 k x t) (app y t)
def opAt (k a b y x : B) : B := integral a b (kernelTimes k y x)
def fredholm (k g l a b y : B) : B :=
  and (le a b) (allR fun x => imp (inI a b x) (and (integrable (kernelTimes k y x) a b)
    (eq (app y x) (add (app g x) (mul l (opAt k a b y x))))))
def any (_ : B) : B := tt
/-- The domain of an argument that speaks about the four arguments before it (as `Build.dom4`). -/
def dom5 (t : Ty) (p : B → B → B → B → B → B) : Option Tm :=
  match close (lamR fun a => lamR fun b => lamR fun c => lamR fun d => lamR fun _ =>
      lamT t (fun _ => tt) fun self => p a b c d self) with
  | .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ inner)))) => some inner
  | _ => none

def vocab : Vocab where
  mods := [
    { phrase := phrase!"solution of the Volterra integral equation with kernel $v$ and right-hand side $v$ from $v$",
      prenominal := false, ty := F,
      pred := close <| lamT F2 any fun k => lamT F any fun g => lamR fun a => lamT F any fun y =>
        allR fun x => imp (le a x) (and (integrable (kernelTimes k y x) a x) (eq (app y x) (add (app g x) (opAt k a x y x)))),
      doc := "`y(x) = g(x) + ∫_a^x K(x,t) y(t) dt` for every `x ≥ a`" },
    { phrase := phrase!"solution of the Fredholm integral equation with kernel $v$, right-hand side $v$ and parameter $v$ on $[v,v]$",
      prenominal := false, ty := F,
      pred := close <| lamT F2 any fun k => lamT F any fun g => lamR fun l => lamR fun a => lamR fun b => lamT F any fun y =>
        fredholm k g l a b y,
      doc := "`y(x) = g(x) + λ ∫_a^b K(x,t) y(t) dt` for every `x ∈ [a,b]`" },
    { phrase := phrase!"solution of the homogeneous Fredholm integral equation with kernel $v$ and parameter $v$ on $[v,v]$",
      prenominal := false, ty := F,
      pred := close <| lamT F2 any fun k => lamR fun l => lamR fun a => lamR fun b => lamT F any fun y =>
        fredholm k (lamR fun _ => num 0) l a b y,
      doc := "`y(x) = λ ∫_a^b K(x,t) y(t) dt` for every `x ∈ [a,b]`" },
    { phrase := phrase!"solution of Abel's integral equation with right-hand side $v$ from $v$", prenominal := false, ty := F,
      pred := close <| lamT F any fun g => lamR fun a => lamT F any fun y =>
        allR fun x => imp (lt a x) (and (integrable (lamR fun t => div (app y t) (sqrt (sub x t))) a x)
          (eq (integral a x (lamR fun t => div (app y t) (sqrt (sub x t)))) (app g x))),
      doc := "`∫_a^x y(t)/√(x-t) dt = g(x)` for every `x > a`" },
    { phrase := phrase!"symmetric kernel", prenominal := false, ty := F2,
      pred := close <| lamT F2 any fun k => allR fun x => allR fun t => eq (app2 k x t) (app2 k t x),
      doc := "`K(x,t) = K(t,x)`" },
    { phrase := phrase!"kernel of Volterra type", prenominal := false, ty := F2,
      pred := close <| lamT F2 any fun k => allR fun x => allR fun t => imp (lt x t) (eq (app2 k x t) (num 0)),
      doc := "`K(x,t) = 0` for `t > x`" }]
  notions := [
    { name := phrase!"second iterated kernel of $v$ on $[v,v]$", ty := F2 ⟶ .real ⟶ .real ⟶ F2,
      doc := "`(x,t) ↦ ∫_a^b K(x,s) K(s,t) ds`",
      value := close <| lamT F2 any fun k => lamR fun a => lamR fun b => lamR fun x => lamR fun t =>
        integral a b (lamR fun s => mul (app2 k x s) (app2 k s t)) },
    { name := phrase!"integral of $v$ against the kernel $v$ on $[v,v]$ at $v$", ty := F ⟶ F2 ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, none, none, dom5 .real fun y k a b x => and (le a b) (integrable (kernelTimes k y x) a b)],
      doc := "`∫_a^b K(x,t) y(t) dt`, the integral operator with kernel `K` applied to `y`, at `x`",
      value := close <| lamT F any fun y => lamT F2 any fun k => lamR fun a => lamR fun b =>
        lamT .real (fun x => and (le a b) (integrable (kernelTimes k y x) a b)) fun x => opAt k a b y x }]

end Leanify.IntegralEquations
