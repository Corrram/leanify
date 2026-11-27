import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Leanify.Denote

/-! # The meaning of the field `solids`

The solids as sets of the Euclidean space `ℝ^n` (`EuclideanSpace ℝ (Fin n)`): balls and spheres,
the cylinder, the cone, the ellipsoid and the torus by their equations, the regular polyhedra
as convex hulls of their vertices, the standard simplex. A volume is the Lebesgue measure of
the solid (Mathlib `volume`), a surface area the `d`-dimensional Euclidean Hausdorff measure of
its boundary (Mathlib `μHE[d]`, the Hausdorff measure scaled to agree with the Lebesgue measure of
`ℝ^d`): the area of a surface (the length of a curve, the number of points of a finite set). The formulas (`π^{n/2} r^n/Γ(n/2 + 1)`, `2π r(r + h)`, …) are theorems, not
definitions. -/

namespace Leanify.Solids

noncomputable section
open MeasureTheory

/-- The Euclidean space of dimension `n`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The volume of a set of `ℝ^n` (its Lebesgue measure). -/
def vol {n : ℕ} (s : Set (E n)) : ℝ := (volume s).toReal

/-- The `d`-dimensional area of a set of `ℝ^n`: its `d`-dimensional Euclidean Hausdorff measure
(Mathlib `μHE[d]`). -/
def area {n : ℕ} (d : ℕ) (s : Set (E n)) : ℝ := (Measure.euclideanHausdorffMeasure d s).toReal

/-- The volume of the ball of radius `r` in dimension `n`. -/
def ballVolume (r n : ℝ) : ℝ := vol (Metric.ball (0 : E ⌊n⌋₊) r)

/-- The surface area of the sphere of radius `r` in dimension `n` (in `ℝ^n`). -/
def sphereArea (r n : ℝ) : ℝ := area (⌊n⌋₊ - 1) (Metric.sphere (0 : E ⌊n⌋₊) r)

/-- The solid cylinder with radius `r` and height `h`, about the third axis. -/
def cylinder (r h : ℝ) : Set (E 3) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2 ∧ 0 ≤ x 2 ∧ x 2 ≤ h}

/-- The solid cone with radius `r` and height `h`: its base the disk of radius `r` in the plane
`x₃ = 0`, its apex at height `h` on the third axis. -/
def cone (r h : ℝ) : Set (E 3) := {x | 0 ≤ x 2 ∧ x 2 ≤ h ∧ h * Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ r * (h - x 2)}

def cylinderVolume (r h : ℝ) : ℝ := vol (cylinder r h)
def cylinderArea (r h : ℝ) : ℝ := area 2 (frontier (cylinder r h))
def coneVolume (r h : ℝ) : ℝ := vol (cone r h)
def coneArea (r h : ℝ) : ℝ := area 2 (frontier (cone r h))

/-- The volume of the solid ellipsoid with semi-axes `a`, `b` and `c`. -/
def ellipsoidVolume (a b c : ℝ) : ℝ := vol {x : E 3 | (x 0 / a) ^ 2 + (x 1 / b) ^ 2 + (x 2 / c) ^ 2 ≤ 1}

/-- The volume of the solid torus with radii `R` (from the axis to the centre of the tube) and
`r` (of the tube). -/
def torusVolume (R r : ℝ) : ℝ := vol {x : E 3 | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 ≤ r ^ 2}

/-- The golden ratio. -/
def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- The points `s • (x, y, z)` for the given triples. -/
def scaled (s : ℝ) (ps : List (ℝ × ℝ × ℝ)) : Set (E 3) := {v | ∃ p ∈ ps, v = s • !₂[p.1, p.2.1, p.2.2]}

/-- The points `(±x, ±y, ±z)`, with all the signs. -/
def signs (x y z : ℝ) : List (ℝ × ℝ × ℝ) :=
  [1, -1].flatMap fun a => [1, -1].flatMap fun b => [1, -1].map fun c => (a * x, b * y, c * z)

/-- The cyclic permutations of `(x, y, z)` with all the signs. -/
def cyclicSigns (x y z : ℝ) : List (ℝ × ℝ × ℝ) := signs x y z ++ signs y z x ++ signs z x y

/-- The regular tetrahedron with edge `a`: the convex hull of `(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)`,
`(-1,-1,1)`, scaled by `a/(2√2)`. -/
def tetrahedron (a : ℝ) : Set (E 3) :=
  convexHull ℝ (scaled (a / (2 * Real.sqrt 2)) [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)])

/-- The regular octahedron with edge `a`: the convex hull of `±e₁, ±e₂, ±e₃` scaled by `a/√2`. -/
def octahedron (a : ℝ) : Set (E 3) :=
  convexHull ℝ (scaled (a / Real.sqrt 2) [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)])

/-- The regular dodecahedron with edge `a`: the convex hull of `(±1, ±1, ±1)` and the cyclic
permutations of `(0, ±1/φ, ±φ)`, scaled by `aφ/2`. -/
def dodecahedron (a : ℝ) : Set (E 3) :=
  convexHull ℝ (scaled (a * φ / 2) (signs 1 1 1 ++ cyclicSigns 0 (1 / φ) φ))

/-- The regular icosahedron with edge `a`: the convex hull of the cyclic permutations of
`(0, ±1, ±φ)`, scaled by `a/2`. -/
def icosahedron (a : ℝ) : Set (E 3) := convexHull ℝ (scaled (a / 2) (cyclicSigns 0 1 φ))

def tetrahedronVolume (a : ℝ) : ℝ := vol (tetrahedron a)
def octahedronVolume (a : ℝ) : ℝ := vol (octahedron a)
def dodecahedronVolume (a : ℝ) : ℝ := vol (dodecahedron a)
def icosahedronVolume (a : ℝ) : ℝ := vol (icosahedron a)

/-- The volume of the standard simplex in dimension `n`: the points of `ℝ^n` with nonnegative
coordinates of sum at most `1`. -/
def simplexVolume (n : ℝ) : ℝ := vol {x : E ⌊n⌋₊ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

end

end Leanify.Solids
