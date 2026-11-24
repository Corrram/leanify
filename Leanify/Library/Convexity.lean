import Leanify.Library.Core

/-! # Vocabulary: generalized convexity

The classes of functions that the literature on Hermite–Hadamard and Jensen type
inequalities works with, each by its defining inequality for a real function on its
natural domain (`Let $f$ be a harmonically convex function.`, `$f$ is $h$-convex`).

* adjectives: `log-convex` (`f > 0`, `f(tx + (1-t)y) ≤ f(x)^t f(y)^{1-t}`), `harmonically
  convex` and `harmonically concave` (on `(0,∞)`: `f(xy/(tx + (1-t)y)) ≤ t f(y) + (1-t) f(x)`),
  `geometrically convex` (on `(0,∞)`, positive: `f(x^t y^{1-t}) ≤ f(x)^t f(y)^{1-t}`),
  `GA-convex` (on `(0,∞)`: `f(x^t y^{1-t}) ≤ t f(x) + (1-t) f(y)`), `star-shaped` (on
  `[0,∞)`: `f(tx) ≤ t f(x)`), `quasiconcave`, `$s$-convex in the second sense` (on `[0,∞)`,
  `0 < s ≤ 1`: `f(tx + (1-t)y) ≤ t^s f(x) + (1-t)^s f(y)`), `$h$-convex` (Varošanec: `f ≥ 0`,
  `f(tx + (1-t)y) ≤ h(t) f(x) + h(1-t) f(y)` for `t ∈ (0,1)`), `P-function`
  (`f ≥ 0`, `f(tx + (1-t)y) ≤ f(x) + f(y)`), `Godunova-Levin function` (`f ≥ 0`,
  `f(tx + (1-t)y) ≤ f(x)/t + f(y)/(1-t)` for `t ∈ (0,1)`), `Wright-convex` (`f(x + δ) - f(x)`
  nondecreasing in `x` for every `δ > 0`), `Jensen-convex with weights` is midpoint
  convexity of the field `functionalequations`;
* notions: the integral mean of `f` on `[a,b]` (`(1/(b-a)) ∫_a^b f`), the Hermite–Hadamard
  gap of `f` on `[a,b]` (`(f(a)+f(b))/2 - (1/(b-a))∫_a^b f`), the Jensen gap of `f` at `x`
  and `y` with weight `t`.

Every meaning is a term of the core language. -/

namespace Leanify.Convexity
open Build Core

abbrev F : Ty := Ty.rfun

def rpow (x y : B) : B := app2 (prim .rpow) x y
def unit (t : B) (body : B) : B := imp (and (le (num 0) t) (le t (num 1))) body
def openUnit (t : B) (body : B) : B := imp (and (lt (num 0) t) (lt t (num 1))) body
def comb (t x y : B) : B := add (mul t x) (mul (sub (num 1) t) y)
/-- For all `x`, `y` with `p x`, `p y` and `t` in `[0,1]`. -/
def all3 (p : Option (B → B)) (body : B → B → B → B) : B :=
  allR fun x => allR fun y => allR fun t => match p with
    | some p => imp (and (p x) (p y)) (unit t (body x y t))
    | none => unit t (body x y t)
def all3o (p : Option (B → B)) (body : B → B → B → B) : B :=
  allR fun x => allR fun y => allR fun t => match p with
    | some p => imp (and (p x) (p y)) (openUnit t (body x y t))
    | none => openUnit t (body x y t)
def pos (x : B) : B := lt (num 0) x
def nonneg (x : B) : B := le (num 0) x
def nonnegFn (f : B) : B := allR fun x => le (num 0) (app f x)
def posFn (f : B) : B := allR fun x => lt (num 0) (app f x)
def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred := fPred body, doc }
def harm (x y t : B) : B := div (mul x y) (comb t x y)
def geo (x y t : B) : B := mul (rpow x t) (rpow y (sub (num 1) t))
def integral (a b f : B) : B := app2 (app (prim .intervalIntegral) a) b f
def mean (a b f : B) : B := div (integral a b f) (sub b a)
def interval (a b f : B) : B :=
  and (lt a b) (app2 (app (prim .intervalIntegrable) f) a b)

def vocab : Vocab where
  mods := [
    adj phrase!"log-convex" true (fun f => and (posFn f) (all3 none fun x y t => le (app f (comb t x y)) (geo (app f x) (app f y) t)))
      "`f > 0` and `f(tx + (1-t)y) ≤ f(x)^t f(y)^{1-t}`, `log f` convex",
    adj phrase!"harmonically convex" true (fun f => all3 (some pos) fun x y t => le (app f (harm x y t)) (comb t (app f y) (app f x)))
      "on `(0,∞)`: `f(xy/(tx + (1-t)y)) ≤ t f(y) + (1-t) f(x)` (İşcan)",
    adj phrase!"harmonically concave" true (fun f => all3 (some pos) fun x y t => le (comb t (app f y) (app f x)) (app f (harm x y t)))
      "on `(0,∞)`: `f(xy/(tx + (1-t)y)) ≥ t f(y) + (1-t) f(x)`",
    adj phrase!"geometrically convex" true
      (fun f => and (allR fun x => imp (pos x) (pos (app f x))) (all3 (some pos) fun x y t => le (app f (geo x y t)) (geo (app f x) (app f y) t)))
      "on `(0,∞)`, positive: `f(x^t y^{1-t}) ≤ f(x)^t f(y)^{1-t}` (multiplicatively convex)",
    adj phrase!"GA-convex" true (fun f => all3 (some pos) fun x y t => le (app f (geo x y t)) (comb t (app f x) (app f y)))
      "on `(0,∞)`: `f(x^t y^{1-t}) ≤ t f(x) + (1-t) f(y)`",
    adj phrase!"star-shaped" true (fun f => allR fun x => allR fun t => imp (nonneg x) (unit t (le (app f (mul t x)) (mul t (app f x)))))
      "on `[0,∞)`: `f(tx) ≤ t f(x)` for `t ∈ [0,1]`",
    adj phrase!"quasiconcave" true (fun f => all3 none fun x y t => le (app2 (prim .min) (app f x) (app f y)) (app f (comb t x y)))
      "`f(tx + (1-t)y) ≥ min(f(x), f(y))`",
    { phrase := phrase!"$v$-convex in the second sense", prenominal := false, ty := F,
      pred := close <| lamR fun s => lamT F (fun _ => tt) fun f =>
        and (and (lt (num 0) s) (le s (num 1)))
          (all3 (some nonneg) fun x y t => le (app f (comb t x y)) (add (mul (rpow t s) (app f x)) (mul (rpow (sub (num 1) t) s) (app f y)))),
      doc := "on `[0,∞)`, `0 < s ≤ 1`: `f(tx + (1-t)y) ≤ t^s f(x) + (1-t)^s f(y)` (Breckner)" },
    { phrase := phrase!"$v$-convex", prenominal := true, ty := F,
      pred := close <| lamT F (fun _ => tt) fun h => lamT F (fun _ => tt) fun f =>
        and (nonnegFn f) (all3o none fun x y t => le (app f (comb t x y)) (add (mul (app h t) (app f x)) (mul (app h (sub (num 1) t)) (app f y)))),
      doc := "for a function `h`: `f ≥ 0`, `f(tx + (1-t)y) ≤ h(t) f(x) + h(1-t) f(y)` for `t ∈ (0,1)` (Varošanec)" },
    adj phrase!"P-function" false (fun f => and (nonnegFn f) (all3 none fun x y t => le (app f (comb t x y)) (add (app f x) (app f y))))
      "`f ≥ 0`, `f(tx + (1-t)y) ≤ f(x) + f(y)` (Dragomir, Pečarić, Persson)",
    adj phrase!"Godunova-Levin function" false
      (fun f => and (nonnegFn f) (all3o none fun x y t => le (app f (comb t x y)) (add (div (app f x) t) (div (app f y) (sub (num 1) t)))))
      "`f ≥ 0`, `f(tx + (1-t)y) ≤ f(x)/t + f(y)/(1-t)` for `t ∈ (0,1)`",
    adj phrase!"Wright-convex" true
      (fun f => allR fun d => imp (pos d) (allR fun x => allR fun y => imp (le x y)
        (le (sub (app f (add x d)) (app f x)) (sub (app f (add y d)) (app f y)))))
      "`f(x + δ) - f(x)` is nondecreasing in `x` for every `δ > 0`"]
  notions := [
    { name := phrase!"integral mean of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun f a b => interval a b f],
      doc := "`(1/(b-a)) ∫_a^b f`, for `a < b` and `f` integrable on `[a,b]`; `[a,b]` is written as the interval",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamT .real (fun b => interval a b f) fun b => mean a b f },
    { name := phrase!"Hermite-Hadamard gap of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun f a b => interval a b f],
      doc := "`(f(a) + f(b))/2 - (1/(b-a)) ∫_a^b f`, nonnegative for a convex `f`",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamT .real (fun b => interval a b f) fun b =>
        sub (div (add (app f a) (app f b)) (num 2)) (mean a b f) },
    { name := phrase!"Jensen gap of $v$ at $v$ and $v$ with weight $v$", ty := F ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`t f(x) + (1-t) f(y) - f(tx + (1-t)y)`",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun x => lamR fun y => lamR fun t =>
        sub (comb t (app f x) (app f y)) (app f (comb t x y)) }]

end Leanify.Convexity
