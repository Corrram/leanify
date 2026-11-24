import Leanify.Library.Risk

/-! # Vocabulary: stochastic orders of densities

The comparisons of two distributions on the line that probability, reliability and
actuarial science use, for the probability densities of the field `densities` (`Let $f$ and
$g$ be probability densities.`): `$f$ is smaller than $g$ in the usual stochastic order`.

* `stochastically smaller than $g$`, `smaller than $g$ in the usual stochastic order`:
  `S_f(x) ≤ S_g(x)` for every `x` (Shaked–Shanthikumar `≤_st`);
* `smaller than $g$ in the hazard rate order`: `S_f(y) S_g(x) ≤ S_f(x) S_g(y)` for `x ≤ y`
  (`S_g/S_f` is nondecreasing, `≤_hr`);
* `smaller than $g$ in the likelihood ratio order`: `f(y) g(x) ≤ f(x) g(y)` for `x ≤ y`
  (`g/f` is nondecreasing, `≤_lr`);
* `smaller than $g$ in the increasing convex order`: finite means and `π_f(d) ≤ π_g(d)`
  for the stop-loss transforms, for every `d` (`≤_icx`);
* `smaller than $g$ in the convex order`: moreover equal means (`≤_cx`).

The ratio orders are written without quotients, so that they are meaningful where a
density or a survival function vanishes. Every meaning is a term of the core language. -/

namespace Leanify.StochasticOrders
open Build Core
open Leanify.Risk (surv stopLoss)
open Leanify.Densities (finiteMean mean)

abbrev F : Ty := Ty.rfun

def st (f g : B) : B := allR fun x => le (surv f x) (surv g x)
def hr (f g : B) : B := allR fun x => allR fun y => imp (le x y) (le (mul (surv f y) (surv g x)) (mul (surv f x) (surv g y)))
def lr (f g : B) : B := allR fun x => allR fun y => imp (le x y) (le (mul (app f y) (app g x)) (mul (app f x) (app g y)))
def icx (f g : B) : B := and (and (finiteMean f) (finiteMean g)) (allR fun d => le (stopLoss f d) (stopLoss g d))
def cx (f g : B) : B := and (icx f g) (eq (mean f) (mean g))

/-- `f` (the subject) is smaller than `g` (the argument): `P g f`. -/
def order (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamT F (fun _ => tt) fun g => lamT F (fun _ => tt) fun f => body f g }

def vocab : Vocab where
  mods := [
    order phrase!"stochastically smaller than $v$" st "`S_f(x) ≤ S_g(x)` for every `x` (`f ≤_st g`)",
    order phrase!"smaller than $v$ in the usual stochastic order" st "`S_f(x) ≤ S_g(x)` for every `x` (`f ≤_st g`)",
    order phrase!"stochastically larger than $v$" (fun f g => st g f) "`S_g(x) ≤ S_f(x)` for every `x` (`g ≤_st f`)",
    order phrase!"larger than $v$ in the usual stochastic order" (fun f g => st g f) "`g ≤_st f`",
    order phrase!"smaller than $v$ in the hazard rate order" hr
      "`S_f(y) S_g(x) ≤ S_f(x) S_g(y)` for `x ≤ y`: `S_g/S_f` is nondecreasing (`f ≤_hr g`)",
    order phrase!"smaller than $v$ in the likelihood ratio order" lr
      "`f(y) g(x) ≤ f(x) g(y)` for `x ≤ y`: `g/f` is nondecreasing (`f ≤_lr g`)",
    order phrase!"smaller than $v$ in the increasing convex order" icx
      "finite means, `π_f(d) ≤ π_g(d)` for every `d` (`f ≤_icx g`)",
    order phrase!"smaller than $v$ in the convex order" cx
      "finite and equal means, `π_f(d) ≤ π_g(d)` for every `d` (`f ≤_cx g`)"]

end Leanify.StochasticOrders
