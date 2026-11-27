import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Leanify.Denote

/-! # The meaning of the field `triangles`

Triangles and regular polygons as figures of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.
A quantity of the triangle with sides `a`, `b`, `c` is its value for every triangle `PQR` of the
plane with `|QR| = a`, `|PR| = b`, `|PQ| = c` (they are congruent): the area of the convex hull
(Lebesgue measure), the angle at `R` (Mathlib `EuclideanGeometry.angle`), the inradius,
circumradius and height of the simplex `PQR` (Mathlib `Affine.Simplex.inradius`,
`circumradius`, `height`), the distance from `R` to the midpoint of `PQ`, and from `R` to the
point of `PQ` that bisects the angle at `R`. The regular polygon with `n` sides of length `s` has
the vertices `ρ(cos(2πk/n), sin(2πk/n))` for the radius `ρ > 0` that makes its sides `s`. The
formulas (Heron, the law of cosines, `abc/(4Δ)`, `(n-2)π/n`, …) are theorems, not
definitions. -/

namespace Leanify.Triangles

noncomputable section
open EuclideanGeometry MeasureTheory

/-- The Euclidean plane. -/
abbrev Pl : Type := EuclideanSpace ℝ (Fin 2)

/-- `PQR` is a triangle with sides `a = |QR|`, `b = |PR|`, `c = |PQ|`. -/
def HasSides (P Q R : Pl) (a b c : ℝ) : Prop := dist Q R = a ∧ dist P R = b ∧ dist P Q = c

/-- The value of a quantity of the triangles with sides `a`, `b`, `c`: the value that it has for
every triangle of the plane with these sides, where there is one (`0` otherwise). -/
def ofSides (a b c : ℝ) (f : Pl → Pl → Pl → ℝ) : ℝ := by
  classical exact
  if h : ∃ v : ℝ, (∃ P Q R : Pl, HasSides P Q R a b c) ∧ ∀ P Q R : Pl, HasSides P Q R a b c → f P Q R = v then
    Classical.choose h
  else 0

/-- A quantity of the simplex `PQR` (`0` if its points are collinear). -/
def ofSimplex (f : Affine.Simplex ℝ Pl 2 → ℝ) (P Q R : Pl) : ℝ := by
  classical exact if h : AffineIndependent ℝ ![P, Q, R] then f ⟨![P, Q, R], h⟩ else 0

/-- The area of the triangle with sides `a`, `b`, `c`. -/
def area (a b c : ℝ) : ℝ := ofSides a b c fun P Q R => (volume (convexHull ℝ {P, Q, R})).toReal

/-- The angle opposite `c` in the triangle with sides `a` and `b`: the angle at the vertex where
the sides `a` and `b` meet. -/
def angleOpposite (c a b : ℝ) : ℝ := ofSides a b c fun P Q R => ∠ P R Q

/-- The inradius of the triangle with sides `a`, `b`, `c`. -/
def inradius (a b c : ℝ) : ℝ := ofSides a b c (ofSimplex fun s => s.inradius)

/-- The circumradius of the triangle with sides `a`, `b`, `c`. -/
def circumradius (a b c : ℝ) : ℝ := ofSides a b c (ofSimplex fun s => s.circumradius)

/-- The altitude to `c` in the triangle with sides `a` and `b`: the height of the vertex opposite
the side `c`. -/
def altitude (c a b : ℝ) : ℝ := ofSides a b c (ofSimplex fun s => s.height 2)

/-- The median to `c` in the triangle with sides `a` and `b`: the distance from the vertex
opposite `c` to the midpoint of `c`. -/
def median (c a b : ℝ) : ℝ := ofSides a b c fun P Q R => dist R (midpoint ℝ P Q)

/-- The bisector of the angle opposite `c` in the triangle with sides `a` and `b`: the distance
from the vertex opposite `c` to the point of the side `c` that bisects the angle there. -/
def bisector (c a b : ℝ) : ℝ := ofSides a b c fun P Q R => by
  classical exact
  if h : ∃ D ∈ segment ℝ P Q, ∠ P R D = ∠ D R Q then dist R (Classical.choose h) else 0

/-- The vertices of the regular polygon with `n` sides on the circle of radius `ρ` about the
origin. -/
def vertex (n : ℕ) (ρ : ℝ) (k : ℕ) : Pl :=
  !₂[ρ * Real.cos (2 * Real.pi * k / n), ρ * Real.sin (2 * Real.pi * k / n)]

/-- The value of a quantity of the regular polygon with `n` sides of length `s`: for the radius
`ρ > 0` that makes the sides `s` (`0` where there is none). -/
def ofPolygon (n : ℕ) (s : ℝ) (f : ℝ → ℝ) : ℝ := by
  classical exact if h : ∃ ρ : ℝ, 0 < ρ ∧ dist (vertex n ρ 0) (vertex n ρ 1) = s then f (Classical.choose h) else 0

/-- The interior angle of the regular polygon with `n` sides of length `s`: the angle at a vertex
between its two neighbours. -/
def interiorAngle (n s : ℝ) : ℝ :=
  ofPolygon ⌊n⌋₊ s fun ρ => ∠ (vertex ⌊n⌋₊ ρ (⌊n⌋₊ - 1)) (vertex ⌊n⌋₊ ρ 0) (vertex ⌊n⌋₊ ρ 1)

/-- The area of the regular polygon with `n` sides of length `s`: of the convex hull of its
vertices. -/
def polygonArea (n s : ℝ) : ℝ :=
  ofPolygon ⌊n⌋₊ s fun ρ => (volume (convexHull ℝ (Set.range fun k : Fin ⌊n⌋₊ => vertex ⌊n⌋₊ ρ k))).toReal

/-- The circumradius of the regular polygon with `n` sides of length `s`: the radius of the
circle through its vertices. -/
def polygonCircumradius (n s : ℝ) : ℝ := ofPolygon ⌊n⌋₊ s fun ρ => by
  classical exact
  if h : ∃ r : ℝ, ∃ c : Pl, ∀ k : Fin ⌊n⌋₊, dist (vertex ⌊n⌋₊ ρ k) c = r then Classical.choose h else 0

/-- The apothem of the regular polygon with `n` sides of length `s`: the distance from its centre
to a side. -/
def apothem (n s : ℝ) : ℝ := ofPolygon ⌊n⌋₊ s fun ρ => Metric.infDist (0 : Pl) (segment ℝ (vertex ⌊n⌋₊ ρ 0) (vertex ⌊n⌋₊ ρ 1))

/-- The number of diagonals of a convex polygon with `n` vertices: the pairs of its vertices that
are not the ends of a side (the edges of the complement of the cycle). -/
def diagonals (n : ℝ) : ℝ := (Nat.card (SimpleGraph.cycleGraph ⌊n⌋₊)ᶜ.edgeSet : ℝ)

end

end Leanify.Triangles
