import Leanify.Library.Core

/-! # Vocabulary: fractional calculus

Fractional integrals and derivatives of a real function on the line, as in the literature
on fractional differential equations and on Hermite–Hadamard inequalities for fractional
integrals (`We write $J^\alpha_a(f,x)$ for the left-sided Riemann-Liouville fractional
integral of order $\alpha$ of $f$ from $a$ at $x$.`).

* notions, for an order `α > 0`: the left-sided Riemann–Liouville fractional integral of `f`
  from `a` at `x > a`, `(1/Γ(α)) ∫_a^x (x-t)^{α-1} f(t) dt`; the right-sided one up to `b`
  at `x < b`, `(1/Γ(α)) ∫_x^b (t-x)^{α-1} f(t) dt`; the Hadamard fractional integral from
  `a > 0`, `(1/Γ(α)) ∫_a^x (log(x/t))^{α-1} f(t)/t dt`; for `0 < α < 1`, the
  Riemann–Liouville fractional derivative (the derivative of the integral of order `1-α`)
  and the Caputo fractional derivative `(1/Γ(1-α)) ∫_a^x (x-t)^{-α} f'(t) dt`; the
  Mittag-Leffler function `E_α(z) = ∑_{k≥0} z^k/Γ(αk+1)` and the two-parameter one
  `E_{α,β}`; the gamma function `Γ(α) = ∫_0^∞ t^{α-1} e^{-t} dt` for `α > 0`.

Each integral is the integral of the core language, and the quantity is defined where its
integrand is integrable (and a derivative where it exists). -/

namespace Leanify.Fractional
open Build Core

abbrev F : Ty := Ty.rfun

def rpow (x y : B) : B := app2 (prim .rpow) x y
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def pos (x : B) : B := lt (num 0) x
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def integrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b
def posRay : B := lamR fun t => lt (num 0) t
def gamma (s : B) : B := app2 (prim .integralOn) posRay (lamR fun t => mul (rpow t (sub s (num 1))) (exp (neg t)))
def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def series (a : B) (body : B → B) : B := app2 (prim .series) a (lamR body)
def seriesConv (a : B) (body : B → B) : B := app2 (prim .seriesConv) a (lamR body)

def leftKernel (al f x : B) : B := lamR fun t => mul (rpow (sub x t) (sub al (num 1))) (app f t)
def rightKernel (al f x : B) : B := lamR fun t => mul (rpow (sub t x) (sub al (num 1))) (app f t)
def hadamardKernel (al f x : B) : B := lamR fun t => div (mul (rpow (log (div x t)) (sub al (num 1))) (app f t)) t
def leftDom (al f a x : B) : B := and (lt a x) (integrable (leftKernel al f x) a x)
def left (al f a x : B) : B := div (integral a x (leftKernel al f x)) (gamma al)
def unitOrder (al : B) : B := and (lt (num 0) al) (lt al (num 1))
/-- `y ↦ J^{1-α}_a f(y)`, for `y > a` (and `0` elsewhere: only its derivative at `x > a`
matters, which the domain asks for near `x`). -/
def leftFn (al f a : B) : B := lamR fun y => left al f a y
def rlDom (al f a x : B) : B :=
  and (lt a x) (and (allR fun y => imp (lt a y) (integrable (leftKernel (sub (num 1) al) f y) a y))
    (diffAt (leftFn (sub (num 1) al) f a) x))
def caputoKernel (al f x : B) : B := lamR fun t => mul (rpow (sub x t) (neg al)) (deriv f t)
def caputoDom (al f a x : B) : B :=
  and (lt a x) (and (allR fun t => imp (and (le a t) (le t x)) (diffAt f t)) (integrable (caputoKernel al f x) a x))
def mlTerm (al be z k : B) : B := div (app2 (prim .zpow) z k) (gamma (add (mul al k) be))

def vocab : Vocab where
  notions := [
    { name := phrase!"gamma function at $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`Γ(s) = ∫_0^∞ t^{s-1} e^{-t} dt`, `s > 0` (Mathlib `Real.Gamma`)",
      value := close <| lamT .real pos gamma },
    { name := phrase!"left-sided Riemann-Liouville fractional integral of order $v$ of $v$ from $v$ at $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none, none, dom4 .real fun al f a x => leftDom al f a x],
      doc := "`(1/Γ(α)) ∫_a^x (x-t)^{α-1} f(t) dt`, `α > 0`, `x > a`, the integrand integrable",
      value := close <| lamT .real pos fun al => lamT F (fun _ => tt) fun f => lamR fun a =>
        lamT .real (fun x => leftDom al f a x) fun x => left al f a x },
    { name := phrase!"right-sided Riemann-Liouville fractional integral of order $v$ of $v$ up to $v$ at $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none, none, dom4 .real fun al f b x => and (lt x b) (integrable (rightKernel al f x) x b)],
      doc := "`(1/Γ(α)) ∫_x^b (t-x)^{α-1} f(t) dt`, `α > 0`, `x < b`",
      value := close <| lamT .real pos fun al => lamT F (fun _ => tt) fun f => lamR fun b =>
        lamT .real (fun x => and (lt x b) (integrable (rightKernel al f x) x b)) fun x =>
          div (integral x b (rightKernel al f x)) (gamma al) },
    { name := phrase!"Hadamard fractional integral of order $v$ of $v$ from $v$ at $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none, dom1 .real pos, dom4 .real fun al f a x => and (lt a x) (integrable (hadamardKernel al f x) a x)],
      doc := "`(1/Γ(α)) ∫_a^x (log(x/t))^{α-1} f(t)/t dt`, `α > 0`, `0 < a < x`",
      value := close <| lamT .real pos fun al => lamT F (fun _ => tt) fun f => lamT .real pos fun a =>
        lamT .real (fun x => and (lt a x) (integrable (hadamardKernel al f x) a x)) fun x =>
          div (integral a x (hadamardKernel al f x)) (gamma al) },
    { name := phrase!"Riemann-Liouville fractional derivative of order $v$ of $v$ from $v$ at $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real unitOrder, none, none, dom4 .real fun al f a x => rlDom al f a x],
      doc := "`d/dx J^{1-α}_a f(x)`, `0 < α < 1`, where the integral of order `1-α` is differentiable at `x`",
      value := close <| lamT .real unitOrder fun al => lamT F (fun _ => tt) fun f => lamR fun a =>
        lamT .real (fun x => rlDom al f a x) fun x => deriv (leftFn (sub (num 1) al) f a) x },
    { name := phrase!"Caputo fractional derivative of order $v$ of $v$ from $v$ at $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real unitOrder, none, none, dom4 .real fun al f a x => caputoDom al f a x],
      doc := "`(1/Γ(1-α)) ∫_a^x (x-t)^{-α} f'(t) dt`, `0 < α < 1`, `f` differentiable on `[a,x]`",
      value := close <| lamT .real unitOrder fun al => lamT F (fun _ => tt) fun f => lamR fun a =>
        lamT .real (fun x => caputoDom al f a x) fun x => div (integral a x (caputoKernel al f x)) (gamma (sub (num 1) al)) },
    { name := phrase!"Mittag-Leffler function with parameter $v$", ty := .real ⟶ F, doms := [dom1 .real pos],
      doc := "`E_α(z) = ∑_{k≥0} z^k/Γ(αk+1)`, `α > 0` (where the series converges, which it does for every `z`)",
      value := close <| lamT .real pos fun al => lamR fun z => series (num 0) fun k => mlTerm al (num 1) z k },
    { name := phrase!"Mittag-Leffler function with parameters $v$ and $v$", ty := .real ⟶ .real ⟶ F,
      doms := [dom1 .real pos, dom1 .real pos],
      doc := "`E_{α,β}(z) = ∑_{k≥0} z^k/Γ(αk+β)`, `α, β > 0`",
      value := close <| lamT .real pos fun al => lamT .real pos fun be => lamR fun z => series (num 0) fun k => mlTerm al be z k }]

end Leanify.Fractional
