import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Leanify.Denote

/-! # The meaning of the field `latticepoints`

The integer points of the plane and of space, counted as elements of `ℤ²` and `ℤ³` (`Nat.card`):
in the disk and the ball, on a segment of `EuclideanSpace ℝ (Fin 2)`, and the visible ones (with
no lattice point strictly between them and the origin). A lattice polygon is a closed polygonal
curve with vertices in `ℤ²` whose sides meet only at their common ends; its region is the curve
with the bounded connected components of its complement (the Jordan curve theorem makes it one
component). Its area is the Lebesgue measure of the region. The formulas (`gcd(a,b) + 1`,
coprime coordinates, Pick's `I + B/2 - 1`) are theorems, not definitions. -/

namespace Leanify.LatticePoints

noncomputable section
open MeasureTheory

/-- The Euclidean plane. -/
abbrev Pl : Type := EuclideanSpace ℝ (Fin 2)

/-- The point of the plane with integer coordinates `p`. -/
def lat (p : ℤ × ℤ) : Pl := !₂[(p.1 : ℝ), (p.2 : ℝ)]

/-- The number of lattice points in the closed disk of radius `r` about the origin. -/
def diskPoints (r : ℝ) : ℝ := (Nat.card {p : ℤ × ℤ // (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ r ^ 2} : ℝ)

/-- The number of lattice points in the closed ball of radius `r` about the origin. -/
def ballPoints (r : ℝ) : ℝ :=
  (Nat.card {p : ℤ × ℤ × ℤ // (p.1 : ℝ) ^ 2 + (p.2.1 : ℝ) ^ 2 + (p.2.2 : ℝ) ^ 2 ≤ r ^ 2} : ℝ)

/-- The number of lattice points on the segment from the origin to `(a, b)`, its ends included. -/
def segmentPoints (a b : ℝ) : ℝ := (Nat.card {p : ℤ × ℤ // lat p ∈ segment ℝ (0 : Pl) !₂[a, b]} : ℝ)

/-- The number of visible lattice points in the square of side `n`: the `(a, b)` with
`1 ≤ a, b ≤ n` with no lattice point strictly between them and the origin. -/
def visiblePoints (n : ℝ) : ℝ :=
  (Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ (p.1 : ℝ) ≤ n ∧ 1 ≤ p.2 ∧ (p.2 : ℝ) ≤ n ∧
    ∀ q : ℤ × ℤ, lat q ∉ openSegment ℝ (0 : Pl) (lat p)} : ℝ)

/-- The side `i` of the closed polygonal curve with the vertices `v`. -/
def side {k : ℕ} (v : Fin (k + 3) → ℤ × ℤ) (i : Fin (k + 3)) : Set Pl := segment ℝ (lat (v i)) (lat (v (i + 1)))

/-- The curve: the union of the sides. -/
def curve {k : ℕ} (v : Fin (k + 3) → ℤ × ℤ) : Set Pl := ⋃ i, side v i

/-- The curve is simple: two sides meet only at the common end of consecutive sides. -/
def IsSimple {k : ℕ} (v : Fin (k + 3) → ℤ × ℤ) : Prop :=
  ∀ i j : Fin (k + 3), i ≠ j → side v i ∩ side v j ⊆
    (if j = i + 1 then {lat (v j)} else ∅) ∪ (if i = j + 1 then {lat (v i)} else ∅)

/-- The region of the polygon: the curve and the bounded connected components of its
complement. -/
def region {k : ℕ} (v : Fin (k + 3) → ℤ × ℤ) : Set Pl :=
  curve v ∪ {x | x ∉ curve v ∧ Bornology.IsBounded (connectedComponentIn (curve v)ᶜ x)}

/-- `v` is a lattice polygon with `I` interior and `B` boundary lattice points. -/
def IsLatticePolygon {k : ℕ} (v : Fin (k + 3) → ℤ × ℤ) (I B : ℝ) : Prop :=
  IsSimple v ∧ (Nat.card {p : ℤ × ℤ // lat p ∈ region v ∧ lat p ∉ curve v} : ℝ) = I ∧
    (Nat.card {p : ℤ × ℤ // lat p ∈ curve v} : ℝ) = B

/-- There is a lattice polygon with `I` interior and `B` boundary points. -/
def ExistsLatticePolygon (I B : ℝ) : Prop := ∃ (k : ℕ) (v : Fin (k + 3) → ℤ × ℤ), IsLatticePolygon v I B

/-- The area of a lattice polygon with `I` interior and `B` boundary points: of every one of them,
where there is one. -/
def pickArea (I B : ℝ) : ℝ := by
  classical exact
  if h : ∃ a : ℝ, ExistsLatticePolygon I B ∧
      ∀ (k : ℕ) (v : Fin (k + 3) → ℤ × ℤ), IsLatticePolygon v I B → (volume (region v)).toReal = a then
    Classical.choose h
  else 0

end

end Leanify.LatticePoints
