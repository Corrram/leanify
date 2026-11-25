import Leanify.Library.Core

/-! # Vocabulary: spherical geometry

Distances, areas and angles on the sphere, by latitudes and longitudes, angles and radii (`We
write $d(\phi_1,\phi_2,\lambda_1,\lambda_2)$ for the central angle between the points with
latitudes $\phi_1$ and $\phi_2$ and longitudes $\lambda_1$ and $\lambda_2$.`).

* notions: the central angle `arccos(sin φ₁ sin φ₂ + cos φ₁ cos φ₂ cos(λ₁ - λ₂))` between two
  points of the unit sphere given by latitude and longitude (the great-circle distance on the
  unit sphere); the chord `2R sin(θ/2)` for a central angle `θ`; the spherical excess
  `α + β + γ - π` and the area `R²(α + β + γ - π)` of a spherical triangle with angles `α`, `β`,
  `γ` (Girard); the area `2πRh` and the volume `πh²(3R - h)/3` of a spherical cap of height
  `h`; the solid angle `2π(1 - cos θ)` of a cone with half-angle `θ`.

Every meaning is a term of the core language. -/

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
def cap (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real fun h => le (num 0) h, dom2 .real fun h r => and (pos r) (le h (mul (num 2) r))], doc,
    value := close <| lamT .real (fun h => le (num 0) h) fun h => lamT .real (fun r => and (pos r) (le h (mul (num 2) r))) fun r => body h r }

def vocab : Vocab where
  notions := [
    { name := phrase!"central angle between the points with latitudes $v$ and $v$ and longitudes $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real lat, dom2 .real fun _ y => lat y, none, none],
      doc := "`arccos(sin φ₁ sin φ₂ + cos φ₁ cos φ₂ cos(λ₁ - λ₂))`: the `θ ∈ [0, π]` with that cosine, the great-circle distance on the unit sphere",
      value := close <| lamT .real lat fun p => lamT .real lat fun q => lamR fun l => lamR fun m =>
        theR fun t => and (and (le (num 0) t) (le t pi))
          (eq (cos t) (add (mul (sin p) (sin q)) (mul (mul (cos p) (cos q)) (cos (sub l m))))) },
    { name := phrase!"chord for the central angle $v$ on a sphere of radius $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => and (le (num 0) t) (le t pi), dom2 .real fun _ r => pos r],
      doc := "`2R sin(θ/2)`",
      value := close <| lamT .real (fun t => and (le (num 0) t) (le t pi)) fun t => lamT .real pos fun r =>
        mul (mul (num 2) r) (sin (div t (num 2))) },
    { name := phrase!"spherical excess of the triangle with angles $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real angle, dom2 .real fun _ b => angle b, dom3 .real triangle],
      doc := "`α + β + γ - π`, for angles in `(0, π)` with `α + β + γ > π`",
      value := close <| lamT .real angle fun a => lamT .real angle fun b => lamT .real (fun c => triangle a b c) fun c => excess a b c },
    { name := phrase!"area of the spherical triangle with angles $v$, $v$ and $v$ on a sphere of radius $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real angle, dom2 .real fun _ b => angle b, dom3 .real triangle, dom4 .real fun _ _ _ r => pos r],
      doc := "`R²(α + β + γ - π)` (Girard's theorem)",
      value := close <| lamT .real angle fun a => lamT .real angle fun b => lamT .real (fun c => triangle a b c) fun c =>
        lamT .real pos fun r => mul (mul r r) (excess a b c) },
    cap phrase!"area of the spherical cap of height $v$ on a sphere of radius $v$" (fun h r => mul (mul (num 2) pi) (mul r h))
      "`2πRh`, for `0 ≤ h ≤ 2R`",
    cap phrase!"volume of the spherical cap of height $v$ on a sphere of radius $v$"
      (fun h r => div (mul pi (mul (mul h h) (sub (mul (num 3) r) h))) (num 3)) "`πh²(3R - h)/3`",
    { name := phrase!"solid angle of a cone with half-angle $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun t => and (le (num 0) t) (le t pi)],
      doc := "`2π(1 - cos θ)`",
      value := close <| lamT .real (fun t => and (le (num 0) t) (le t pi)) fun t => mul (mul (num 2) pi) (sub (num 1) (cos t)) }]

end Leanify.SphericalGeometry
