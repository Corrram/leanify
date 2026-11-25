import Leanify.Library.Core

/-! # Vocabulary: volumes and surface areas of solids

The volumes and surface areas of the standard solids, and of balls and spheres in `n`
dimensions (`We write $V_n(r)$ for the volume of the ball of radius $r$ in dimension $n$.`).

* notions: the volume `π^{n/2} r^n/Γ(n/2 + 1)` of the ball of radius `r` in `ℝ^n` and the surface
  area `2π^{n/2} r^{n-1}/Γ(n/2)` of its boundary sphere; the volume and surface area of a cylinder
  (`π r² h`, `2π r(r + h)`) and of a cone (`π r² h/3`, `π r(r + √(r² + h²))`); the volume of an
  ellipsoid with semi-axes `a, b, c` (`4π abc/3`) and of a torus with radii `R > r`
  (`2π² R r²`); the volumes of the regular tetrahedron, octahedron, dodecahedron and
  icosahedron with edge `a`; the volume `1/n!` of the standard simplex in `ℝ^n`.

`Γ` is the integral `∫_0^∞ t^{s-1} e^{-t} dt`; every meaning is a term of the core language. -/

namespace Leanify.Solids
open Build Core

def rpow (x y : B) : B := app2 (prim .rpow) x y
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def exp (x : B) : B := app (prim (.realFn .exp)) x
def pi : B := prim .pi
def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def posRay : B := lamR fun t => lt (num 0) t
def gamma (s : B) : B := app2 (prim .integralOn) posRay (lamR fun t => mul (rpow t (sub s (num 1))) (exp (neg t)))
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real pos], doc,
    value := close <| lamT .real pos fun r => lamT .real pos fun h => body r h }
def edge (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := close <| lamT .real pos body }
def cube (a : B) : B := mul a (mul a a)

def vocab : Vocab where
  notions := [
    { name := phrase!"volume of the ball of radius $v$ in dimension $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r, dom1 .real posInt], doc := "`π^{n/2} r^n/Γ(n/2 + 1)`",
      value := close <| lamT .real (fun r => le (num 0) r) fun r => lamT .real posInt fun n =>
        div (mul (rpow pi (div n (num 2))) (rpow r n)) (gamma (add (div n (num 2)) (num 1))) },
    { name := phrase!"surface area of the sphere of radius $v$ in dimension $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r, dom1 .real posInt], doc := "`2π^{n/2} r^{n-1}/Γ(n/2)`, the sphere in `ℝ^n`",
      value := close <| lamT .real (fun r => le (num 0) r) fun r => lamT .real posInt fun n =>
        div (mul (mul (num 2) (rpow pi (div n (num 2)))) (rpow r (sub n (num 1)))) (gamma (div n (num 2))) },
    two phrase!"volume of the cylinder with radius $v$ and height $v$" (fun r h => mul (mul pi (mul r r)) h) "`π r² h`",
    two phrase!"surface area of the cylinder with radius $v$ and height $v$" (fun r h => mul (mul (num 2) (mul pi r)) (add r h))
      "`2π r(r + h)`",
    two phrase!"volume of the cone with radius $v$ and height $v$" (fun r h => div (mul (mul pi (mul r r)) h) (num 3)) "`π r² h/3`",
    two phrase!"surface area of the cone with radius $v$ and height $v$"
      (fun r h => mul (mul pi r) (add r (sqrt (add (mul r r) (mul h h))))) "`π r(r + √(r² + h²))`",
    { name := phrase!"volume of the ellipsoid with semi-axes $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom1 .real pos, dom1 .real pos], doc := "`4π abc/3`",
      value := close <| lamT .real pos fun a => lamT .real pos fun b => lamT .real pos fun c =>
        div (mul (mul (num 4) pi) (mul (mul a b) c)) (num 3) },
    { name := phrase!"volume of the torus with radii $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun bigR r => and (pos r) (lt r bigR)], doc := "`2π² R r²`, `0 < r < R`",
      value := close <| lamT .real pos fun bigR => lamT .real (fun r => and (pos r) (lt r bigR)) fun r =>
        mul (mul (mul (num 2) (mul pi pi)) bigR) (mul r r) },
    edge phrase!"volume of the regular tetrahedron with edge $v$" (fun a => div (cube a) (mul (num 6) (sqrt (num 2)))) "`a³/(6√2)`",
    edge phrase!"volume of the regular octahedron with edge $v$" (fun a => div (mul (sqrt (num 2)) (cube a)) (num 3)) "`√2 a³/3`",
    edge phrase!"volume of the regular dodecahedron with edge $v$"
      (fun a => div (mul (add (num 15) (mul (num 7) (sqrt (num 5)))) (cube a)) (num 4)) "`(15 + 7√5) a³/4`",
    edge phrase!"volume of the regular icosahedron with edge $v$"
      (fun a => div (mul (mul (num 5) (add (num 3) (sqrt (num 5)))) (cube a)) (num 12)) "`5(3 + √5) a³/12`",
    { name := phrase!"volume of the standard simplex in dimension $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`1/n!`", value := close <| lamT .real posInt fun n => div (num 1) (app (prim .factorial) n) }]

end Leanify.Solids
