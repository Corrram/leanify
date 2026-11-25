import Leanify.Library.Core

/-! # Vocabulary: geometric probability

Expectations and probabilities for independent uniform random points, as integrals over the
regions where the points lie (`We write $D$ for the expected distance between two random points
in the unit square.`). Each is the integral itself (Mathlib's Lebesgue integral over `ℝⁿ`), so that
a closed form such as `(2 + √2 + 5 log(1 + √2))/15` is a claim to be proved, not a definition.
Buffon's needle is in the field `classicalprobability`.

* notions: the expected distance between two independent uniform points in the unit interval, in
  the unit square and in the unit disk; the expected area of a triangle with independent uniform
  vertices in the unit square; the probability that three independent uniform points on a circle
  form an acute triangle.

Every meaning is a term of the core language. -/

namespace Leanify.GeometricProbability
open Build Core

def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def unit (x : B) : B := and (le (num 0) x) (le x (num 1))
def ind (p : B) (v : B) : B := cases p v (num 0)
/-- `∫_{ℝⁿ} f`, for `f` integrable (otherwise undefined). -/
def integral (n : Nat) (f : B) : B := theR fun r => app2 (prim (.integralN n)) f r
def sq (x : B) : B := mul x x
def inDisk (x y : B) : B := le (add (sq x) (sq y)) (num 1)
def constant (name : Phrase) (v : B) (doc : String) : Notion := { name, ty := .real, doc, value := close v }
/-- The point `(cos t, sin t)` and the dot product of `B - A` and `C - A`. -/
def dotAt (a b c : B) : B :=
  add (mul (sub (cos b) (cos a)) (sub (cos c) (cos a))) (mul (sub (sin b) (sin a)) (sub (sin c) (sin a)))
def angle (t : B) : B := and (le (num 0) t) (lt t (mul (num 2) pi))

def vocab : Vocab where
  notions := [
    constant phrase!"expected distance between two random points in the unit interval"
      (integral 2 (lamR fun x => lamR fun y => ind (and (unit x) (unit y)) (abs (sub x y))))
      "`∫₀¹∫₀¹ |x - y| dx dy` (which is `1/3`)",
    constant phrase!"expected distance between two random points in the unit square"
      (integral 4 (lamR fun a => lamR fun b => lamR fun c => lamR fun d =>
        ind (and (and (unit a) (unit b)) (and (unit c) (unit d))) (sqrt (add (sq (sub a c)) (sq (sub b d))))))
      "`∫_{[0,1]⁴} |P - Q|` (which is `(2 + √2 + 5 log(1 + √2))/15`)",
    constant phrase!"expected distance between two random points in the unit disk"
      (div (integral 4 (lamR fun a => lamR fun b => lamR fun c => lamR fun d =>
        ind (and (inDisk a b) (inDisk c d)) (sqrt (add (sq (sub a c)) (sq (sub b d)))))) (mul pi pi))
      "`(1/π²)∫_{D×D} |P - Q|` (which is `128/(45π)`)",
    constant phrase!"expected area of a triangle with random vertices in the unit square"
      (integral 6 (lamR fun a => lamR fun b => lamR fun c => lamR fun d => lamR fun e => lamR fun f =>
        ind (and (and (and (unit a) (unit b)) (and (unit c) (unit d))) (and (unit e) (unit f)))
          (div (abs (sub (mul (sub c a) (sub f b)) (mul (sub e a) (sub d b)))) (num 2))))
      "`∫_{[0,1]⁶} area(PQR)` (which is `11/144`)",
    constant phrase!"probability that three random points on a circle form an acute triangle"
      (div (integral 3 (lamR fun a => lamR fun b => lamR fun c =>
        ind (and (and (angle a) (angle b)) (angle c))
          (cases (and (and (lt (num 0) (dotAt a b c)) (lt (num 0) (dotAt b c a))) (lt (num 0) (dotAt c a b))) (num 1) (num 0))))
        (mul (mul (mul (num 2) pi) (mul (num 2) pi)) (mul (num 2) pi)))
      "`(2π)^{-3}` times the measure of the angles `(α, β, γ) ∈ [0, 2π)³` whose points form an acute triangle (which is `1/4`)"]

end Leanify.GeometricProbability
