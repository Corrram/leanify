import Leanify.Library.Core

/-! # Vocabulary: convergence acceleration and iteration counts

Extrapolations, estimated orders and the iteration counts of the basic methods (`We write
$N(L,t)$ for the number of bisection steps for an interval of
length $L$ and tolerance $t$.`). Iterative methods as sequences are in the field `iteration`.

* notions: the number `⌈log₂(L/ε)⌉` of bisection steps; the number `⌈log(ε/e₀)/log q⌉` of steps of
  a contraction with constant `q`; the Richardson extrapolation `(2^p A(h/2) - A(h))/(2^p - 1)`;
  Aitken's extrapolation `x - (y-x)²/(z - 2y + x)`; the estimated order of convergence
  `log(e₂/e₁)/log(e₁/e₀)` from three errors; the number `-log₁₀(|x̂ - x|/|x|)` of correct
  significant digits.

Every meaning is a term of the core language. -/

namespace Leanify.Convergence
open Build Core

def pos (x : B) : B := lt (num 0) x
def log (x : B) : B := app (prim (.realFn .log)) x
def ceil (x : B) : B := app (prim .ceil) x
def zpow (x k : B) : B := app2 (prim .zpow) x k

def vocab : Vocab where
  notions := [
    { name := phrase!"number of bisection steps for an interval of length $v$ and tolerance $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun l e => and (pos e) (lt e l)],
      doc := "`⌈log₂(L/ε)⌉`: the steps after which the bracketing interval is shorter than `ε`",
      value := close <| lamT .real pos fun l => lamT .real (fun e => and (pos e) (lt e l)) fun e => ceil (div (log (div l e)) (log (num 2))) },
    { name := phrase!"number of steps of a contraction with constant $v$ from the error $v$ to the tolerance $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun q => and (pos q) (lt q (num 1)), dom2 .real fun _ e => pos e, dom3 .real fun _ e t => and (pos t) (lt t e)],
      doc := "`⌈log(ε/e₀)/log q⌉`",
      value := close <| lamT .real (fun q => and (pos q) (lt q (num 1))) fun q => lamT .real pos fun e => lamT .real (fun t => and (pos t) (lt t e)) fun t =>
        ceil (div (log (div t e)) (log q)) },
    { name := phrase!"Richardson extrapolation of the approximations $v$ and $v$ of order $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun _ _ p => and (isInt p) (le (num 1) p)],
      doc := "`(2^p A(h/2) - A(h))/(2^p - 1)` for `A(h)` and `A(h/2)`",
      value := close <| lamR fun a => lamR fun b => lamT .real (fun p => and (isInt p) (le (num 1) p)) fun p =>
        div (sub (mul (zpow (num 2) p) b) a) (sub (zpow (num 2) p) (num 1)) },
    { name := phrase!"Aitken extrapolation of $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun x y z => ne (add (sub z (mul (num 2) y)) x) (num 0)],
      doc := "`x - (y-x)²/(z - 2y + x)` (Aitken's Δ²)",
      value := close <| lamR fun x => lamR fun y => lamT .real (fun z => ne (add (sub z (mul (num 2) y)) x) (num 0)) fun z =>
        sub x (div (mul (sub y x) (sub y x)) (add (sub z (mul (num 2) y)) x)) },
    { name := phrase!"estimated order of convergence from the errors $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun a b => and (pos b) (ne b a), dom3 .real fun _ _ c => pos c],
      doc := "`log(e₂/e₁)/log(e₁/e₀)`",
      value := close <| lamT .real pos fun a => lamT .real (fun b => and (pos b) (ne b a)) fun b => lamT .real pos fun c =>
        div (log (div c b)) (log (div b a)) },
    { name := phrase!"number of correct significant digits of $v$ as an approximation of $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun a x => and (ne x (num 0)) (ne a x)],
      doc := "`-log₁₀(|x̂ - x|/|x|)`",
      value := close <| lamR fun a => lamT .real (fun x => and (ne x (num 0)) (ne a x)) fun x =>
        neg (div (log (div (abs (sub a x)) (abs x))) (log (num 10))) }]

end Leanify.Convergence
