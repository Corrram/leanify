import Leanify.Library.Core

/-! # Vocabulary: surfaces

The topology and curvature of the standard surfaces (`We write $\chi(g)$ for the Euler
characteristic of the closed orientable surface of genus $g$.`).

* notions: the Euler characteristic `2 - 2g` of the closed orientable and `2 - k` of the closed
  nonorientable surface of genus `g`, `k`, and the genus `(2 - χ)/2` of a closed orientable
  surface; the total curvature `4π(1 - g)` (Gauss–Bonnet); the Gaussian curvature `1/R²` and the
  mean curvature `1/R` of a sphere, the mean curvature `1/(2R)` of a cylinder; the surface area
  `4π²Rr` of a torus and its Gaussian curvature `cos θ/(r(R + r cos θ))` at the angle `θ` from
  the outer equator.

Every meaning is a term of the core language. -/

namespace Leanify.Surfaces
open Build Core

def pos (x : B) : B := lt (num 0) x
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def radius (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := close <| lamT .real pos body }

def vocab : Vocab where
  notions := [
    { name := phrase!"Euler characteristic of the closed orientable surface of genus $v$", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "`2 - 2g`", value := close <| lamT .real natP fun g => sub (num 2) (mul (num 2) g) },
    { name := phrase!"Euler characteristic of the closed nonorientable surface of genus $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`2 - k`: the connected sum of `k` projective planes", value := close <| lamT .real posInt fun k => sub (num 2) k },
    { name := phrase!"genus of the closed orientable surface with Euler characteristic $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun c => and (isInt c) (and (le c (num 2)) (isInt (div c (num 2))))],
      doc := "`(2 - χ)/2`, for an even `χ ≤ 2`",
      value := close <| lamT .real (fun c => and (isInt c) (and (le c (num 2)) (isInt (div c (num 2))))) fun c => div (sub (num 2) c) (num 2) },
    { name := phrase!"total curvature of the closed orientable surface of genus $v$", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "`4π(1 - g)` = `2πχ` (Gauss–Bonnet)", value := close <| lamT .real natP fun g => mul (mul (num 4) pi) (sub (num 1) g) },
    radius phrase!"Gaussian curvature of the sphere of radius $v$" (fun r => div (num 1) (mul r r)) "`1/R²`",
    radius phrase!"mean curvature of the sphere of radius $v$" (fun r => div (num 1) r) "`1/R`",
    radius phrase!"mean curvature of the cylinder of radius $v$" (fun r => div (num 1) (mul (num 2) r)) "`1/(2R)`",
    { name := phrase!"surface area of the torus with radii $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun a r => and (pos r) (lt r a)],
      doc := "`4π²Rr`, for the distance `R` from the axis to the centre of the tube and the tube radius `r < R`",
      value := close <| lamT .real pos fun a => lamT .real (fun r => and (pos r) (lt r a)) fun r => mul (mul (num 4) (mul pi pi)) (mul a r) },
    { name := phrase!"Gaussian curvature of the torus with radii $v$ and $v$ at the angle $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun a r => and (pos r) (lt r a), none],
      doc := "`cos θ/(r(R + r cos θ))`, `θ` measured from the outer equator",
      value := close <| lamT .real pos fun a => lamT .real (fun r => and (pos r) (lt r a)) fun r => lamR fun t =>
        div (cos t) (mul r (add a (mul r (cos t)))) }]

end Leanify.Surfaces
