import Leanify.Library.Core

/-! # Vocabulary: iterative methods

Root finding and fixed-point iteration for real functions, and the speed of convergence of
a sequence. A sequence is a real function whose values at the natural numbers are its
terms (`x(n)`, written `x_n` where the article declares it so), as in the core's
`\lim_{n\to\infty}`.

* notions: the Newton map of `f` (`x ↦ x - f(x)/f'(x)`, where `f'(x) ≠ 0`), the secant
  step of `f` from `x` and `y`, the relaxation of `g` with parameter `ω`
  (`x ↦ (1-ω)x + ω g(x)`);
* adjectives of sequences, with the function: `Newton sequence for $f$`, `secant sequence
  for $f$`, `fixed-point sequence of $g$` (each term is the step from the term before);
* adjectives of sequences, with the limit: `convergent to $y$ with order $p$`, `linearly
  convergent to $y$`, `superlinearly convergent to $y$`, `quadratically convergent to $y$`,
  `cubically convergent to $y$`;
* adjectives of functions: `contractive`, `$L$-contractive` (`|g(x) - g(y)| ≤ L|x - y|`,
  `L < 1`).

Every meaning is a term of the core language. An order of convergence is a bound on the
errors `e_n = |x_n - y|`, `e_{n+1} ≤ C e_n^p` for every `n`, together with `e_n → 0`. -/

namespace Leanify.Iteration
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def exUnique (p : B → B) : B := exR fun m => and (p m) (allR fun m' => imp (p m') (eq m' m))
def derivAt (f x : B) : B := theR fun d => hasDeriv f x d
def rpow (x p : B) : B := app2 (prim .rpow) x p
def newtonDom (f x : B) : B := and (exUnique fun d => hasDeriv f x d) (ne (derivAt f x) (num 0))
def newton (f x : B) : B := sub x (div (app f x) (derivAt f x))
def secant (f x y : B) : B := sub x (div (mul (app f x) (sub x y)) (sub (app f x) (app f y)))
def forNat (body : B → B) : B := allR fun n => imp (isNat n) (body n)
def err (a y n : B) : B := abs (sub (app a n) y)
/-- `|a_n - y| → 0` over the natural numbers. -/
def tends (a y : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun n => imp (and (isNat n) (le n0 n)) (lt (err a y n) e))
def orderBound (a y p : B) : B :=
  exR fun c => and (lt (num 0) c) (forNat fun n => le (err a y (add n (num 1))) (mul c (rpow (err a y n) p)))
def lipschitzWith (g l : B) : B := allR fun x => allR fun y => le (abs (sub (app g x) (app g y))) (mul l (abs (sub x y)))

/-- A property of a sequence `a` with a function `f` (`P f a`). -/
def seqOf (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamT F (fun _ => tt) fun f => lamT F (fun _ => tt) fun a => body f a }
/-- A property of a sequence `a` with its limit `y` (`P y a`). -/
def seqTo (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamR fun y => lamT F (fun _ => tt) fun a => body a y }

def vocab : Vocab where
  mods := [
    seqOf phrase!"Newton sequence for $v$"
      (fun f a => forNat fun n => and (newtonDom f (app a n)) (eq (app a (add n (num 1))) (newton f (app a n))))
      "`x_{n+1} = x_n - f(x_n)/f'(x_n)`, `f'(x_n) ≠ 0`, for every `n`",
    seqOf phrase!"secant sequence for $v$"
      (fun f a => forNat fun n => and (ne (app f (app a (add n (num 1)))) (app f (app a n)))
        (eq (app a (add n (num 2))) (secant f (app a (add n (num 1))) (app a n))))
      "`x_{n+2} = x_{n+1} - f(x_{n+1})(x_{n+1} - x_n)/(f(x_{n+1}) - f(x_n))`, with nonzero denominators",
    seqOf phrase!"fixed-point sequence of $v$" (fun g a => forNat fun n => eq (app a (add n (num 1))) (app g (app a n)))
      "`x_{n+1} = g(x_n)` for every `n`",
    { phrase := phrase!"convergent to $v$ with order $v$", prenominal := false, ty := F,
      doc := "`|x_n - y| → 0` and `|x_{n+1} - y| ≤ C|x_n - y|^p` for some `C > 0`, `p ≥ 1`",
      pred := close <| lamR fun y => lamR fun p => lamT F (fun _ => tt) fun a =>
        and (le (num 1) p) (and (tends a y) (orderBound a y p)) },
    seqTo phrase!"linearly convergent to $v$"
      (fun a y => exR fun c => and (and (lt (num 0) c) (lt c (num 1))) (forNat fun n => le (err a y (add n (num 1))) (mul c (err a y n))))
      "`|x_{n+1} - y| ≤ c|x_n - y|` for some `0 < c < 1`",
    seqTo phrase!"superlinearly convergent to $v$"
      (fun a y => and (tends a y) (allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun n =>
        imp (and (isNat n) (le n0 n)) (le (err a y (add n (num 1))) (mul e (err a y n))))))
      "`|x_n - y| → 0` and `|x_{n+1} - y| ≤ ε|x_n - y|` eventually, for every `ε > 0`",
    seqTo phrase!"quadratically convergent to $v$" (fun a y => and (tends a y) (orderBound a y (num 2)))
      "`|x_n - y| → 0` and `|x_{n+1} - y| ≤ C|x_n - y|²`",
    seqTo phrase!"cubically convergent to $v$" (fun a y => and (tends a y) (orderBound a y (num 3)))
      "`|x_n - y| → 0` and `|x_{n+1} - y| ≤ C|x_n - y|³`",
    { phrase := phrase!"contractive", prenominal := true, ty := F,
      pred := close <| lamT F (fun _ => tt) fun g => exR fun l => and (and (le (num 0) l) (lt l (num 1))) (lipschitzWith g l),
      doc := "`|g(x) - g(y)| ≤ L|x - y|` for some `L < 1` (Mathlib `ContractingWith`)" },
    { phrase := phrase!"$v$-contractive", prenominal := true, ty := F,
      pred := close <| lamR fun l => lamT F (fun _ => tt) fun g => and (and (le (num 0) l) (lt l (num 1))) (lipschitzWith g l),
      doc := "`|g(x) - g(y)| ≤ L|x - y|`, `0 ≤ L < 1`" }]
  notions := [
    { name := phrase!"Newton map of $v$", ty := F ⟶ F, doms := [none, dom2 .real newtonDom],
      doc := "`x ↦ x - f(x)/f'(x)`, where `f` is differentiable and `f'(x) ≠ 0`",
      value := close <| lamT F (fun _ => tt) fun f => lamT .real (fun x => newtonDom f x) fun x => newton f x },
    { name := phrase!"secant step of $v$ from $v$ and $v$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun f x y => ne (app f x) (app f y)],
      doc := "`x - f(x)(x - y)/(f(x) - f(y))`, `f(x) ≠ f(y)`",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun x => lamT .real (fun y => ne (app f x) (app f y)) fun y => secant f x y },
    { name := phrase!"relaxation of $v$ with parameter $v$", ty := F ⟶ .real ⟶ F,
      doc := "`x ↦ (1-ω)x + ω g(x)`",
      value := close <| lamT F (fun _ => tt) fun g => lamR fun w => lamR fun x => add (mul (sub (num 1) w) x) (mul w (app g x)) }]

end Leanify.Iteration
