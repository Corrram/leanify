import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Leanify.Denote

/-! # The meaning of the field `surfaces`

Surfaces of `ℝ³` by their parametrizations `X(u, v)`: the Gaussian curvature `(LN - M²)/(EG - F²)`
and the mean curvature `(EN - 2FM + GL)/(2(EG - F²))` of the first fundamental form `E`, `F`, `G`
(the inner products of the partial derivatives `X_u`, `X_v`) and the second `L`, `M`, `N` (those
of the second partial derivatives with the unit normal `X_u × X_v/|X_u × X_v|`, Mathlib `deriv`,
`crossProduct`). The parametrizations of the sphere and the cylinder have the normal towards the
centre and the axis; a curvature of the sphere and the cylinder is its value at every regular
point. The area of the torus is the Euclidean Hausdorff measure (Mathlib `μHE[2]`) of its points.
The values `1/R²`, `1/R`, `1/(2R)`, `4π²Rr` and `cos θ/(r(R + r cos θ))` are theorems, not
definitions. -/

namespace Leanify.Surfaces

noncomputable section
open Matrix

/-- The partial derivatives of a parametrization `X : ℝ × ℝ → ℝ³` at `(u, v)`. -/
def Xu (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ := deriv (fun s => X (s, v)) u
def Xv (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ := deriv (fun s => X (u, s)) v
def Xuu (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ := deriv (fun s => Xu X s v) u
def Xuv (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ := deriv (fun s => Xu X u s) v
def Xvv (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ := deriv (fun s => Xv X u s) v

/-- The unit normal `X_u × X_v/|X_u × X_v|`. -/
def normal (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  let w := crossProduct (Xu X u v) (Xv X u v)
  (1 / Real.sqrt (w ⬝ᵥ w)) • w

/-- The Gaussian curvature of the parametrized surface at `(u, v)`. -/
def gaussCurvature (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  let E := Xu X u v ⬝ᵥ Xu X u v
  let F := Xu X u v ⬝ᵥ Xv X u v
  let G := Xv X u v ⬝ᵥ Xv X u v
  let n := normal X u v
  let L := Xuu X u v ⬝ᵥ n
  let M := Xuv X u v ⬝ᵥ n
  let N := Xvv X u v ⬝ᵥ n
  (L * N - M ^ 2) / (E * G - F ^ 2)

/-- The mean curvature of the parametrized surface at `(u, v)`, for its unit normal. -/
def meanCurvature (X : ℝ × ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  let E := Xu X u v ⬝ᵥ Xu X u v
  let F := Xu X u v ⬝ᵥ Xv X u v
  let G := Xv X u v ⬝ᵥ Xv X u v
  let n := normal X u v
  let L := Xuu X u v ⬝ᵥ n
  let M := Xuv X u v ⬝ᵥ n
  let N := Xvv X u v ⬝ᵥ n
  (E * N - 2 * F * M + G * L) / (2 * (E * G - F ^ 2))

/-- The sphere of radius `R` by latitude `u` and longitude `v` (normal towards the centre). -/
def sphere (R : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![R * Real.cos p.1 * Real.cos p.2, R * Real.cos p.1 * Real.sin p.2, R * Real.sin p.1]

/-- The cylinder of radius `R` by height `u` and angle `v` (normal towards the axis). -/
def cylinder (R : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := ![R * Real.cos p.2, R * Real.sin p.2, p.1]

/-- The torus with radii `R` and `r` by the angle `u` about the axis and the angle `v` from the
outer equator. -/
def torus (R r : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![(R + r * Real.cos p.2) * Real.cos p.1, (R + r * Real.cos p.2) * Real.sin p.1, r * Real.sin p.2]

/-- The value of a curvature at every regular point of the sphere (off the poles), `0` where they
differ. -/
def onSphere (R : ℝ) (k : (ℝ × ℝ → Fin 3 → ℝ) → ℝ → ℝ → ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ∀ u v : ℝ, |u| < Real.pi / 2 → k (sphere R) u v = c then Classical.choose h else 0

/-- The value of a curvature at every point of the cylinder. -/
def onCylinder (R : ℝ) (k : (ℝ × ℝ → Fin 3 → ℝ) → ℝ → ℝ → ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ∀ u v : ℝ, k (cylinder R) u v = c then Classical.choose h else 0

def sphereGauss (R : ℝ) : ℝ := onSphere R gaussCurvature
def sphereMean (R : ℝ) : ℝ := onSphere R meanCurvature
def cylinderMean (R : ℝ) : ℝ := onCylinder R meanCurvature

/-- The Gaussian curvature of the torus at the angle `θ` from the outer equator: its value at
every point at that angle. -/
def torusGauss (R r θ : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ∀ u : ℝ, gaussCurvature (torus R r) u θ = c then Classical.choose h else 0

/-- The surface area of the torus with radii `R` and `r`. -/
def torusArea (R r : ℝ) : ℝ :=
  (MeasureTheory.Measure.euclideanHausdorffMeasure 2
    {x : EuclideanSpace ℝ (Fin 3) | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2}).toReal

end

end Leanify.Surfaces
