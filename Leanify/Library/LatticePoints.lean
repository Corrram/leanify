import Leanify.Library.Core

/-! # Vocabulary: lattice points

Counts of integer points in plane and space regions, and Pick's theorem (`We write $N(r)$ for
the number of lattice points in the disk of radius $r$.`).

* notions: the number of points of `ℤ²` in the closed disk of radius `r` about the origin
  (Gauss's circle problem) and of `ℤ³` in the closed ball; the number `gcd(a,b) + 1` of lattice
  points on the segment from the origin to `(a,b)`; the number of visible lattice points
  `(a,b)` with `1 ≤ a, b ≤ n` (coprime coordinates); the area `I + B/2 - 1` of a lattice
  polygon with `I` interior and `B` boundary points (Pick). The greatest common divisor itself
  is in the field `numbers`.

Every meaning is a term of the core language. -/

namespace Leanify.LatticePoints
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def sq (x : B) : B := mul x x
def ind (p : B) : B := cases p (num 1) (num 0)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def common (d a b : B) : B := and (divides d a) (divides d b)
/-- The greatest common divisor of integers `a`, `b`, not both zero. -/
def gcd (a b : B) : B := theR fun d => and (posInt d) (and (common d a b) (allR fun e => imp (and (posInt e) (common e a b)) (le e d)))
def coprime (a b : B) : B := allR fun d => imp (and (posInt d) (common d a b)) (eq d (num 1))
def notBoth (a b : B) : B := and (and (isInt a) (isInt b)) (or (ne a (num 0)) (ne b (num 0)))

def vocab : Vocab where
  notions := [
    { name := phrase!"number of lattice points in the disk of radius $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r],
      doc := "the number of `(a,b) ∈ ℤ²` with `a² + b² ≤ r²` (Gauss's circle problem)",
      value := close <| lamT .real (fun r => le (num 0) r) fun r =>
        finSum (neg (floor r)) (floor r) fun a => finSum (neg (floor r)) (floor r) fun b => ind (le (add (sq a) (sq b)) (sq r)) },
    { name := phrase!"number of lattice points in the ball of radius $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r],
      doc := "the number of `(a,b,c) ∈ ℤ³` with `a² + b² + c² ≤ r²`",
      value := close <| lamT .real (fun r => le (num 0) r) fun r =>
        finSum (neg (floor r)) (floor r) fun a => finSum (neg (floor r)) (floor r) fun b => finSum (neg (floor r)) (floor r) fun c =>
          ind (le (add (sq a) (add (sq b) (sq c))) (sq r)) },
    { name := phrase!"number of lattice points on the segment from the origin to the point with coordinates $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt, dom2 .real fun a b => notBoth a b],
      doc := "`gcd(a,b) + 1`, with both endpoints",
      value := close <| lamT .real isInt fun a => lamT .real (fun b => notBoth a b) fun b => add (gcd a b) (num 1) },
    { name := phrase!"number of visible lattice points in the square of side $v$", ty := .real ⟶ .real,
      doms := [dom1 .real natP],
      doc := "the number of `(a,b)` with `1 ≤ a, b ≤ n` and `gcd(a,b) = 1`",
      value := close <| lamT .real natP fun n => finSum (num 1) n fun a => finSum (num 1) n fun b => ind (coprime a b) },
    { name := phrase!"area of a lattice polygon with $v$ interior points and $v$ boundary points", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ b => and (isInt b) (le (num 3) b)],
      doc := "`I + B/2 - 1` (Pick's theorem), for a simple polygon with lattice vertices",
      value := close <| lamT .real natP fun i => lamT .real (fun b => and (isInt b) (le (num 3) b)) fun b =>
        sub (add i (div b (num 2))) (num 1) }]

end Leanify.LatticePoints
