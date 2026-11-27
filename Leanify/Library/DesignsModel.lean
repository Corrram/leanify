import Mathlib.Combinatorics.Configuration
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Leanify.Denote

/-! # The meaning of the field `designs`

A `2`-`(v,k,λ)` design is a multiset of blocks, `k`-element subsets of the `v` points `Fin v`,
such that every two distinct points lie in exactly `λ` blocks; a Steiner triple system of order
`v` is a `2`-`(v,3,1)` design. A projective plane of order `n` is Mathlib's
`Configuration.ProjectivePlane` with `order = n`; an affine plane of order `n` is a set of
points with lines (sets of points of `n` elements) such that two distinct points lie on exactly
one line, through a point off a line there is exactly one line not meeting it, and there are
three points on no line. A quantity of such a structure is its value for every one of them,
where there is one. The formulas (`λ(v-1)/(k-1)`, `λv(v-1)/(k(k-1))`, `v(v-1)/6`, `n² + n + 1`,
`n²`, `n² + n`) are theorems, not definitions. -/

namespace Leanify.Designs

noncomputable section

/-- `D` is a `2`-`(v,k,λ)` design on the points `Fin v`. -/
def IsDesign (v k l : ℕ) (D : Multiset (Finset (Fin v))) : Prop :=
  (∀ B ∈ D, B.card = k) ∧ ∀ x y : Fin v, x ≠ y → (D.filter fun B => x ∈ B ∧ y ∈ B).card = l

/-- There is a `2`-`(v,k,λ)` design. -/
def ExistsDesign (v k l : ℝ) : Prop := ∃ D, IsDesign ⌊v⌋₊ ⌊k⌋₊ ⌊l⌋₊ D

/-- The value of a quantity of the `2`-`(v,k,λ)` designs: that of every one of them, where there
is one (`0` otherwise). -/
def ofDesigns (v k l : ℝ) (f : Multiset (Finset (Fin ⌊v⌋₊)) → ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ExistsDesign v k l ∧ ∀ D, IsDesign ⌊v⌋₊ ⌊k⌋₊ ⌊l⌋₊ D → f D = c then Classical.choose h else 0

/-- The replication number of a `2`-`(v,k,λ)` design: the number of blocks through a point (the
same for every point). -/
def replication (v k l : ℝ) : ℝ := ofDesigns v k l fun D => by
  classical exact
  if h : ∃ r : ℝ, ∀ x : Fin ⌊v⌋₊, ((D.filter fun B => x ∈ B).card : ℝ) = r then Classical.choose h else 0

/-- The number of blocks of a `2`-`(v,k,λ)` design. -/
def numBlocks (v k l : ℝ) : ℝ := ofDesigns v k l fun D => (D.card : ℝ)

/-- There is a Steiner triple system of order `v`. -/
def ExistsSTS (v : ℝ) : Prop := ExistsDesign v 3 1

/-- The number of triples of a Steiner triple system of order `v`. -/
def numTriples (v : ℝ) : ℝ := numBlocks v 3 1

/-- `(P, L, ∈)` is a projective plane of order `n` with finitely many points. -/
def IsProjectivePlane (P L : Type) [Membership P L] [Configuration.ProjectivePlane P L] (n : ℕ) : Prop :=
  Finite P ∧ Configuration.ProjectivePlane.order P L = n

/-- There is a projective plane of order `n`. -/
def ExistsProjectivePlane (n : ℝ) : Prop :=
  ∃ (P L : Type) (_ : Membership P L) (_ : Configuration.ProjectivePlane P L), IsProjectivePlane P L ⌊n⌋₊

/-- The number of points of a projective plane of order `n`. -/
def projectivePoints (n : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ExistsProjectivePlane n ∧ ∀ (P L : Type) (_ : Membership P L) (_ : Configuration.ProjectivePlane P L),
      IsProjectivePlane P L ⌊n⌋₊ → (Nat.card P : ℝ) = c then Classical.choose h else 0

/-- The number of lines of a projective plane of order `n`. -/
def projectiveLines (n : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ExistsProjectivePlane n ∧ ∀ (P L : Type) (_ : Membership P L) (_ : Configuration.ProjectivePlane P L),
      IsProjectivePlane P L ⌊n⌋₊ → (Nat.card L : ℝ) = c then Classical.choose h else 0

/-- `L` are the lines of an affine plane of order `n` on the points `P`. -/
def IsAffinePlane (P : Type) (L : Set (Set P)) (n : ℕ) : Prop :=
  Finite P ∧ (∀ l ∈ L, l.ncard = n) ∧
  (∀ x y : P, x ≠ y → ∃! l, l ∈ L ∧ x ∈ l ∧ y ∈ l) ∧
  (∀ l ∈ L, ∀ x : P, x ∉ l → ∃! m, m ∈ L ∧ x ∈ m ∧ Disjoint m l) ∧
  (∃ x y z : P, ¬ ∃ l ∈ L, x ∈ l ∧ y ∈ l ∧ z ∈ l)

/-- There is an affine plane of order `n`. -/
def ExistsAffinePlane (n : ℝ) : Prop := ∃ (P : Type) (L : Set (Set P)), IsAffinePlane P L ⌊n⌋₊

/-- The number of points of an affine plane of order `n`. -/
def affinePoints (n : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ExistsAffinePlane n ∧ ∀ (P : Type) (L : Set (Set P)), IsAffinePlane P L ⌊n⌋₊ → (Nat.card P : ℝ) = c then
    Classical.choose h
  else 0

/-- The number of lines of an affine plane of order `n`. -/
def affineLines (n : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ExistsAffinePlane n ∧ ∀ (P : Type) (L : Set (Set P)), IsAffinePlane P L ⌊n⌋₊ → (L.ncard : ℝ) = c then
    Classical.choose h
  else 0

end

end Leanify.Designs
