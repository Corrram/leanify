import Leanify.Library.Core

/-! # Vocabulary: spherical geometry

Distances, areas and angles on the sphere, by latitudes and longitudes, angles and radii (`We
write $d(\phi_1,\phi_2,\lambda_1,\lambda_2)$ for the central angle between the points with
latitudes $\phi_1$ and $\phi_2$ and longitudes $\lambda_1$ and $\lambda_2$.`).

* notions: the central angle between two points of the unit sphere given by latitude and
  longitude (the great-circle distance on the unit sphere); the chord for a central angle `θ`;
  the spherical excess `α + β + γ - π` and the area of a spherical triangle with angles `α`, `β`,
  `γ`; the area and the volume of a spherical cap of height `h`; the solid angle of a cone with
  half-angle `θ`.

Apart from the spherical excess, the quantities are constants, interpreted by the declarations
of `Leanify/Library/SphericalGeometryModel.lean`: the sphere of `EuclideanSpace ℝ (Fin 3)`, the
angle between two of its points as vectors (Mathlib `InnerProductGeometry.angle`), the
Euclidean Hausdorff measure of its parts (Mathlib `μHE[2]`) and the Lebesgue measure. The
formulas (`arccos(sin φ₁ sin φ₂ + cos φ₁ cos φ₂ cos(λ₁ - λ₂))`, `2R sin(θ/2)`, Girard's
`R²(α + β + γ - π)`, `2πRh`, `πh²(3R - h)/3`, `2π(1 - cos θ)`) are theorems, not definitions. A
spherical triangle with given angles is said to exist where it does. -/

namespace Leanify.SphericalGeometry
open Build Core

def pos (x : B) : B := lt (num 0) x
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def lat (x : B) : B := and (le (neg (div pi (num 2))) x) (le x (div pi (num 2)))
def angle (x : B) : B := and (lt (num 0) x) (lt x pi)
def excess (a b c : B) : B := sub (add a (add b c)) pi
def triangle (a b c : B) : B := and (angle c) (lt pi (add a (add b c)))
def cap (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real fun h => le (num 0) h, dom2 .real fun h r => and (pos r) (le h (mul (num 2) r))], doc,
    value := .const c }
def app3 (f x y z : B) : B := app (app2 f x y) z

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def centralAngle : Nat := 0
def chord : Nat := 1
def triangleArea : Nat := 2
def capArea : Nat := 3
def capVolume : Nat := 4
def solidAngle : Nat := 5
def existsTriangle : Nat := 6
end Const

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .prop]
  constNames := [w!"\\operatorname{ang}", w!"\\operatorname{chord}_{#2}(#1)", w!"\\operatorname{area}_{\\triangle}",
    w!"\\operatorname{area}(\\mathrm{Cap}_{#1,#2})", w!"\\operatorname{vol}(\\mathrm{Cap}_{#1,#2})", w!"\\Omega",
    w!"\\exists\\triangle_{#1,#2,#3}"]
  constLean := [w!"Leanify.SphericalGeometry.centralAngle", w!"Leanify.SphericalGeometry.chord",
    w!"Leanify.SphericalGeometry.triangleArea", w!"Leanify.SphericalGeometry.capArea",
    w!"Leanify.SphericalGeometry.capVolume", w!"Leanify.SphericalGeometry.solidAngle",
    w!"Leanify.SphericalGeometry.ExistsSphTriangle"]
  modules := [w!"Leanify.Library.SphericalGeometryModel"]
  notions := [
    { name := phrase!"central angle between the points with latitudes $v$ and $v$ and longitudes $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real lat, dom2 .real fun _ y => lat y, none, none],
      doc := "the angle between the points `(cos φ cos λ, cos φ sin λ, sin φ)` of the unit sphere as vectors, the great-circle distance (`arccos(sin φ₁ sin φ₂ + cos φ₁ cos φ₂ cos(λ₁ - λ₂))`)",
      value := .const Const.centralAngle },
    { name := phrase!"chord for the central angle $v$ on a sphere of radius $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => and (le (num 0) t) (le t pi), dom2 .real fun _ r => pos r],
      doc := "the distance between two points of the sphere at that central angle (`2R sin(θ/2)`)",
      value := .const Const.chord },
    { name := phrase!"spherical excess of the triangle with angles $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real angle, dom2 .real fun _ b => angle b, dom3 .real triangle],
      doc := "`α + β + γ - π`, for angles in `(0, π)` with `α + β + γ > π`",
      value := close <| lamT .real angle fun a => lamT .real angle fun b => lamT .real (fun c => triangle a b c) fun c => excess a b c },
    { name := phrase!"area of the spherical triangle with angles $v$, $v$ and $v$ on a sphere of radius $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real angle, dom2 .real fun _ b => angle b,
        dom3 .real fun a b c => app3 (const Const.existsTriangle) a b c, dom4 .real fun _ _ _ r => pos r],
      doc := "the Euclidean Hausdorff measure of a spherical triangle with these angles, where there is one (`R²(α + β + γ - π)`, Girard)",
      value := .const Const.triangleArea },
    cap phrase!"area of the spherical cap of height $v$ on a sphere of radius $v$" Const.capArea
      "the area of the points of the sphere at height at least `R - h` (`2πRh`), for `0 ≤ h ≤ 2R`",
    cap phrase!"volume of the spherical cap of height $v$ on a sphere of radius $v$" Const.capVolume
      "the Lebesgue measure of the points of the ball at height at least `R - h` (`πh²(3R - h)/3`)",
    { name := phrase!"solid angle of a cone with half-angle $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun t => and (le (num 0) t) (le t pi)],
      doc := "the area of the part of the unit sphere inside the cone (`2π(1 - cos θ)`)",
      value := .const Const.solidAngle }]

end Leanify.SphericalGeometry
