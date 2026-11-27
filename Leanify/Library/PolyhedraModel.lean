import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Leanify.Denote

/-! # The meaning of the field `polyhedra`

The Platonic solids as convex polyhedra of `EuclideanSpace ℝ (Fin 3)`: the convex hulls of finite
sets with interior points whose faces are regular polygons with `p` sides, `q` of them at each
vertex. A face of dimension `d` is a nonempty exposed subset (Mathlib `IsExposed`) whose affine
span has dimension `d`: the vertices, edges and faces are those of dimension `0`, `1` and `2`. The
dihedral angle is the angle between two faces with a common edge, `π` less the angle between
their outer normals. The counts `4p/D`, `2pq/D`, `4q/D` (`D = 4 - (p-2)(q-2)`) and the dihedral
angle `sin(θ/2) = cos(π/q)/sin(π/p)` are theorems, not definitions. -/

namespace Leanify.Polyhedra

noncomputable section
open EuclideanGeometry

/-- The Euclidean space of dimension `3`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The faces of dimension `d` of a set of `E`: its nonempty exposed subsets whose affine span has
dimension `d`. -/
def faces {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (d : ℕ) : Set (Set (EuclideanSpace ℝ (Fin n))) :=
  {F | F.Nonempty ∧ IsExposed ℝ P F ∧ Module.finrank ℝ (vectorSpan ℝ F) = d}

/-- A convex polyhedron: the convex hull of a finite set of `E3`, with interior points. -/
def IsPolyhedron (P : Set E3) : Prop :=
  (∃ S : Finset E3, P = convexHull ℝ (S : Set E3)) ∧ (interior P).Nonempty

/-- A face of a polyhedron is a regular polygon with `p` sides: it has `p` vertices, all its edges
have the same length and all its angles are equal (the angle at a vertex between its two
edges). -/
def IsRegularPolygon (F : Set E3) (p : ℕ) : Prop :=
  Nat.card (faces F 0) = p ∧
  (∃ ℓ : ℝ, ∀ a b : E3, segment ℝ a b ∈ faces F 1 → dist a b = ℓ) ∧
  (∃ θ : ℝ, ∀ v a b : E3, a ≠ b → segment ℝ v a ∈ faces F 1 → segment ℝ v b ∈ faces F 1 → ∠ a v b = θ)

/-- `P` is a Platonic solid with faces of `p` sides and `q` faces at each vertex. -/
def IsPlatonic (P : Set E3) (p q : ℕ) : Prop :=
  IsPolyhedron P ∧ (∀ F ∈ faces P 2, IsRegularPolygon F p) ∧
    ∀ v : E3, {v} ∈ faces P 0 → Nat.card {F // F ∈ faces P 2 ∧ v ∈ F} = q

/-- There is a Platonic solid with faces of `p` sides and `q` faces at each vertex. -/
def ExistsPlatonic (p q : ℝ) : Prop := ∃ P : Set E3, IsPlatonic P ⌊p⌋₊ ⌊q⌋₊

/-- The value of a quantity of the Platonic solids `{p,q}`: the value it has for every one of
them, where there is one (`0` otherwise). -/
def ofPlatonic (p q : ℝ) (f : Set E3 → ℝ) : ℝ := by
  classical exact
  if h : ∃ v : ℝ, ExistsPlatonic p q ∧ ∀ P : Set E3, IsPlatonic P ⌊p⌋₊ ⌊q⌋₊ → f P = v then
    Classical.choose h
  else 0

def numVertices (p q : ℝ) : ℝ := ofPlatonic p q fun P => (Nat.card (faces P 0) : ℝ)
def numEdges (p q : ℝ) : ℝ := ofPlatonic p q fun P => (Nat.card (faces P 1) : ℝ)
def numFaces (p q : ℝ) : ℝ := ofPlatonic p q fun P => (Nat.card (faces P 2) : ℝ)

/-- `u` is the outer unit normal of the face `F` of `P`: `F` is where `P` is farthest in the
direction `u`. -/
def IsOuterNormal (P F : Set E3) (u : E3) : Prop :=
  ‖u‖ = 1 ∧ ∀ x ∈ P, ∀ y ∈ F, inner ℝ u x ≤ inner ℝ u y

/-- The dihedral angle of the Platonic solid `{p,q}`: between two faces with a common edge, `π`
less the angle between their outer normals. -/
def dihedralAngle (p q : ℝ) : ℝ := ofPlatonic p q fun P => by
  classical exact
  if h : ∃ θ : ℝ, ∀ F G : Set E3, F ∈ faces P 2 → G ∈ faces P 2 → F ∩ G ∈ faces P 1 →
      ∀ u w : E3, IsOuterNormal P F u → IsOuterNormal P G w → Real.pi - InnerProductGeometry.angle u w = θ then
    Classical.choose h
  else 0

end

end Leanify.Polyhedra
