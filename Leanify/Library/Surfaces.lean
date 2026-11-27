import Leanify.Library.Core

/-! # Vocabulary: surfaces

The topology and curvature of the standard surfaces (`We write $\chi(g)$ for the Euler
characteristic of the closed orientable surface of genus $g$.`).

* notions: the Euler characteristic `2 - 2g` of the closed orientable and `2 - k` of the closed
  nonorientable surface of genus `g`, `k`, and the genus `(2 - χ)/2` of a closed orientable
  surface; the total curvature `4π(1 - g)` (Gauss–Bonnet); the Gaussian and the mean curvature
  of a sphere, the mean curvature of a cylinder; the surface area of a torus and its Gaussian
  curvature at the angle `θ` from the outer equator.

The Euler characteristics, the genus and the total curvature of the closed surfaces are their
classical values, terms of the core language (Mathlib has no closed surfaces of every genus to
measure). The curvatures and the area are constants, interpreted by the declarations of
`Leanify/Library/SurfacesModel.lean`: the curvatures of the parametrized sphere, cylinder and
torus by their fundamental forms (Mathlib `deriv`, `crossProduct`), the normal of the sphere
and the cylinder towards the centre and the axis, and the Euclidean Hausdorff measure of the
torus (Mathlib `μHE[2]`). The values `1/R²`, `1/R`, `1/(2R)`, `4π²Rr` and
`cos θ/(r(R + r cos θ))` are theorems, not definitions. -/

namespace Leanify.Surfaces
open Build Core

def pos (x : B) : B := lt (num 0) x
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def radius (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := .const c }

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def sphereGauss : Nat := 0
def sphereMean : Nat := 1
def cylinderMean : Nat := 2
def torusArea : Nat := 3
def torusGauss : Nat := 4
end Const

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real]
  constNames := [w!"K(S_{#})", w!"H(S_{#})", w!"H(Z_{#})", w!"\\operatorname{area}(T_{#1,#2})", w!"K(T_{#1,#2})(#3)"]
  constLean := [w!"Leanify.Surfaces.sphereGauss", w!"Leanify.Surfaces.sphereMean", w!"Leanify.Surfaces.cylinderMean",
    w!"Leanify.Surfaces.torusArea", w!"Leanify.Surfaces.torusGauss"]
  modules := [w!"Leanify.Library.SurfacesModel"]
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
    radius phrase!"Gaussian curvature of the sphere of radius $v$" Const.sphereGauss
      "`(LN - M²)/(EG - F²)` at every regular point of the parametrized sphere (`1/R²`)",
    radius phrase!"mean curvature of the sphere of radius $v$" Const.sphereMean
      "`(EN - 2FM + GL)/(2(EG - F²))`, the normal towards the centre (`1/R`)",
    radius phrase!"mean curvature of the cylinder of radius $v$" Const.cylinderMean
      "the normal towards the axis (`1/(2R)`)",
    { name := phrase!"surface area of the torus with radii $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun a r => and (pos r) (lt r a)],
      doc := "the Euclidean Hausdorff measure of the torus, for the distance `R` from the axis to the centre of the tube and the tube radius `r < R` (`4π²Rr`)",
      value := .const Const.torusArea },
    { name := phrase!"Gaussian curvature of the torus with radii $v$ and $v$ at the angle $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun a r => and (pos r) (lt r a), none],
      doc := "at the points at the angle `θ` from the outer equator (`cos θ/(r(R + r cos θ))`)",
      value := .const Const.torusGauss }]

end Leanify.Surfaces
