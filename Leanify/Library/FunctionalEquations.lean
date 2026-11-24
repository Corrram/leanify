import Leanify.Library.Core

/-! # Vocabulary: functional equations and inequalities

Properties of a real function on the line defined by an equation or an inequality between
its values, as in the study of Cauchy's and Jensen's equations and of subadditivity.

* adjectives: `additive` (`f(x+y) = f(x) + f(y)`), `Cauchy-additive` (the same),
  `subadditive` (`f(x+y) ≤ f(x) + f(y)`), `superadditive`, `midpoint convex`
  (`f((x+y)/2) ≤ (f(x)+f(y))/2`), `midpoint concave`, `Jensen-affine`
  (`f((x+y)/2) = (f(x)+f(y))/2`), `multiplicative on the reals` (`f(xy) = f(x)f(y)`), `involutive` (`f(f(x)) = x`),
  `idempotent` (`f(f(x)) = f(x)`), `homogeneous of degree $k$` (`f(tx) = t^k f(x)`, `t > 0`),
  `positively homogeneous`, `logarithmically additive` (`f(xy) = f(x) + f(y)` for
  `x, y > 0`), `solution of d'Alembert's equation` (`f(x+y) + f(x-y) = 2f(x)f(y)`).

Every meaning is a term of the core language. -/

namespace Leanify.FunctionalEquations
open Build Core

abbrev F : Ty := Ty.rfun

def all2 (body : B → B → B) : B := allR fun x => allR fun y => body x y
def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred := fPred body, doc }
def additive (f : B) : B := all2 fun x y => eq (app f (add x y)) (add (app f x) (app f y))
def mid (x y : B) : B := div (add x y) (num 2)
def homog (k f : B) : B := allR fun t => imp (lt (num 0) t) (allR fun x => eq (app f (mul t x)) (mul (app2 (prim .rpow) t k) (app f x)))

def vocab : Vocab where
  mods := [
    adj phrase!"additive" true additive "`f(x+y) = f(x) + f(y)` (Cauchy's equation; Mathlib `AddMonoidHom`)",
    adj phrase!"Cauchy-additive" true additive "`f(x+y) = f(x) + f(y)`",
    adj phrase!"subadditive" true (fun f => all2 fun x y => le (app f (add x y)) (add (app f x) (app f y))) "`f(x+y) ≤ f(x) + f(y)`",
    adj phrase!"superadditive" true (fun f => all2 fun x y => le (add (app f x) (app f y)) (app f (add x y))) "`f(x+y) ≥ f(x) + f(y)`",
    adj phrase!"midpoint convex" true (fun f => all2 fun x y => le (app f (mid x y)) (mid (app f x) (app f y)))
      "`f((x+y)/2) ≤ (f(x)+f(y))/2` (Jensen-convex)",
    adj phrase!"midpoint concave" true (fun f => all2 fun x y => le (mid (app f x) (app f y)) (app f (mid x y)))
      "`f((x+y)/2) ≥ (f(x)+f(y))/2`",
    adj phrase!"Jensen-affine" true (fun f => all2 fun x y => eq (app f (mid x y)) (mid (app f x) (app f y)))
      "`f((x+y)/2) = (f(x)+f(y))/2` (Jensen's equation)",
    adj phrase!"multiplicative on the reals" false (fun f => all2 fun x y => eq (app f (mul x y)) (mul (app f x) (app f y)))
      "`f(xy) = f(x)f(y)` for all real `x`, `y`",
    adj phrase!"involutive" true (fun f => allR fun x => eq (app f (app f x)) x) "`f(f(x)) = x`",
    adj phrase!"idempotent" true (fun f => allR fun x => eq (app f (app f x)) (app f x)) "`f(f(x)) = f(x)`",
    { phrase := phrase!"homogeneous of degree $v$", prenominal := false, ty := F,
      pred := close <| lamR fun k => lamT F (fun _ => tt) fun f => homog k f, doc := "`f(tx) = t^k f(x)` for `t > 0`" },
    adj phrase!"positively homogeneous" true (homog (num 1)) "`f(tx) = t f(x)` for `t > 0`",
    adj phrase!"logarithmically additive" true
      (fun f => all2 fun x y => imp (and (lt (num 0) x) (lt (num 0) y)) (eq (app f (mul x y)) (add (app f x) (app f y))))
      "`f(xy) = f(x) + f(y)` for `x, y > 0`",
    adj phrase!"solution of d'Alembert's equation" false
      (fun f => all2 fun x y => eq (add (app f (add x y)) (app f (sub x y))) (mul (mul (num 2) (app f x)) (app f y)))
      "`f(x+y) + f(x-y) = 2f(x)f(y)`"]

end Leanify.FunctionalEquations
