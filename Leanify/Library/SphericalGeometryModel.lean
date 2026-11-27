import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Leanify.Denote

/-! # The meaning of the field `sphericalgeometry`

The sphere of radius `R` about the origin of `EuclideanSpace ℝ (Fin 3)`. The point with latitude
`φ` and longitude `λ` is `(cos φ cos λ, cos φ sin λ, sin φ)`; a central angle is the angle
between two points as vectors (Mathlib `InnerProductGeometry.angle`); an area is the Euclidean
Hausdorff measure of a part of the sphere (Mathlib `μHE[2]`) and a volume a Lebesgue measure.
A spherical triangle is the part of the sphere in the cone over three linearly independent
points of it, its angles those between the great circles at its vertices. The formulas (the
spherical law of cosines, `2R sin(θ/2)`, Girard's `R²(α + β + γ - π)`, `2πRh`, `πh²(3R - h)/3`,
`2π(1 - cos θ)`) are theorems, not definitions. -/

namespace Leanify.SphericalGeometry

noncomputable section
open MeasureTheory

/-- The Euclidean space of dimension `3`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The point of the unit sphere with latitude `φ` and longitude `λ`. -/
def point (φ l : ℝ) : E3 := !₂[Real.cos φ * Real.cos l, Real.cos φ * Real.sin l, Real.sin φ]

/-- The central angle between the points with latitudes `φ₁` and `φ₂` and longitudes `λ₁` and
`λ₂`: the angle between them as vectors. -/
def centralAngle (φ₁ φ₂ l₁ l₂ : ℝ) : ℝ := InnerProductGeometry.angle (point φ₁ l₁) (point φ₂ l₂)

/-- The chord for the central angle `θ` on a sphere of radius `R`: the distance between two points
of the sphere at the central angle `θ` (the same for all of them; `0` where there are none). -/
def chord (θ R : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, (∃ u v : E3, ‖u‖ = R ∧ ‖v‖ = R ∧ InnerProductGeometry.angle u v = θ) ∧
      ∀ u v : E3, ‖u‖ = R → ‖v‖ = R → InnerProductGeometry.angle u v = θ → dist u v = c then
    Classical.choose h
  else 0

/-- The spherical triangle with vertices `A`, `B`, `C` of the unit sphere: the points of the unit
sphere in the cone over them. -/
def sphTriangle (A B C : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C}

/-- The angle at `A` of the spherical triangle `ABC`: between the great circles from `A` to `B`
and to `C` (between their tangents at `A`). -/
def sphAngle (A B C : E3) : ℝ :=
  InnerProductGeometry.angle (B - (inner ℝ A B) • A) (C - (inner ℝ A C) • A)

/-- `A`, `B`, `C` are the vertices of a spherical triangle with the angles `α`, `β`, `γ` at them. -/
def IsSphTriangle (A B C : E3) (α β γ : ℝ) : Prop :=
  ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ ‖C‖ = 1 ∧ LinearIndependent ℝ ![A, B, C] ∧
    sphAngle A B C = α ∧ sphAngle B C A = β ∧ sphAngle C A B = γ

/-- There is a spherical triangle with the angles `α`, `β`, `γ`. -/
def ExistsSphTriangle (α β γ : ℝ) : Prop := ∃ A B C : E3, IsSphTriangle A B C α β γ

/-- The area of the spherical triangle with angles `α`, `β`, `γ` on a sphere of radius `R`: of
every such triangle (scaled by `R`). -/
def triangleArea (α β γ R : ℝ) : ℝ := by
  classical exact
  if h : ∃ v : ℝ, ExistsSphTriangle α β γ ∧ ∀ A B C : E3, IsSphTriangle A B C α β γ →
      (Measure.euclideanHausdorffMeasure 2 ((fun x => R • x) '' sphTriangle A B C)).toReal = v then
    Classical.choose h
  else 0

/-- The area of the spherical cap of height `h` on a sphere of radius `R`: the points of the
sphere at height at least `R - h`. -/
def capArea (h R : ℝ) : ℝ :=
  (Measure.euclideanHausdorffMeasure 2 {x : E3 | ‖x‖ = R ∧ R - h ≤ x 2}).toReal

/-- The volume of the spherical cap of height `h` on a sphere of radius `R`: the points of the
ball at height at least `R - h`. -/
def capVolume (h R : ℝ) : ℝ := (volume {x : E3 | ‖x‖ ≤ R ∧ R - h ≤ x 2}).toReal

/-- The solid angle of a cone with half-angle `θ`: the area of the part of the unit sphere inside
the cone about the third axis. -/
def solidAngle (θ : ℝ) : ℝ :=
  (Measure.euclideanHausdorffMeasure 2 {x : E3 | ‖x‖ = 1 ∧ InnerProductGeometry.angle x !₂[0, 0, 1] ≤ θ}).toReal

end

end Leanify.SphericalGeometry
