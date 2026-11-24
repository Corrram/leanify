import Leanify.Denote
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Exponent
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.ZMod.Basic

/-! # The meaning of the field `groups`

A finite group is a group structure on `Fin n`, for some `n`; the groups of Mathlib are
carried to `Fin n` along `Fintype.equivFin`. -/

namespace Leanify.Groups

/-- A group structure on `Fin n`, for some `n`. -/
def Grp : Type := Σ n : ℕ, Group (Fin n)

noncomputable section
open Classical

/-- A finite group of Mathlib, on `Fin n`. -/
def ofGroup (α : Type) [Group α] [Fintype α] : Grp :=
  ⟨Fintype.card α, (Fintype.equivFin α).symm.group⟩

def trivial : Grp := ofGroup Unit

def order (G : Grp) : ℝ := G.1
def Abelian (G : Grp) : Prop := letI := G.2; ∀ a b : Fin G.1, a * b = b * a
def Cyclic (G : Grp) : Prop := letI := G.2; IsCyclic (Fin G.1)
def Simple (G : Grp) : Prop := letI := G.2; IsSimpleGroup (Fin G.1)
def Solvable (G : Grp) : Prop := letI := G.2; Group.IsSolvable (Fin G.1)
def Nilpotent (G : Grp) : Prop := letI := G.2; Group.IsNilpotent (Fin G.1)
def Isomorphic (G H : Grp) : Prop := Nonempty (@MulEquiv (Fin G.1) (Fin H.1) G.2.toMul H.2.toMul)
def PGroup (p : ℝ) (G : Grp) : Prop := letI := G.2; IsPGroup ⌊p⌋₊ (Fin G.1)
def exponent (G : Grp) : ℝ := letI := G.2; Monoid.exponent (Fin G.1)
def numSubgroups (G : Grp) : ℝ := letI := G.2; Nat.card (Subgroup (Fin G.1))
def numNormalSubgroups (G : Grp) : ℝ := letI := G.2; Nat.card {H : Subgroup (Fin G.1) // H.Normal}
def numConjClasses (G : Grp) : ℝ := letI := G.2; Nat.card (ConjClasses (Fin G.1))
def numOfOrder (d : ℝ) (G : Grp) : ℝ := letI := G.2; Nat.card {g : Fin G.1 // orderOf g = ⌊d⌋₊}
def numSylow (p : ℝ) (G : Grp) : ℝ := letI := G.2; Nat.card (Sylow ⌊p⌋₊ (Fin G.1))
def centerOrder (G : Grp) : ℝ := letI := G.2; Nat.card (Subgroup.center (Fin G.1))

def cyclic (n : ℝ) : Grp :=
  if h : ⌊n⌋₊ = 0 then trivial else haveI : NeZero ⌊n⌋₊ := ⟨h⟩; ofGroup (Multiplicative (ZMod ⌊n⌋₊))
def symmetric (n : ℝ) : Grp := ofGroup (Equiv.Perm (Fin ⌊n⌋₊))
def alternating (n : ℝ) : Grp := ofGroup (alternatingGroup (Fin ⌊n⌋₊))
/-- The dihedral group of order `m = 2n`. -/
def dihedral (m : ℝ) : Grp :=
  if h : ⌊m⌋₊ / 2 = 0 then trivial else haveI : NeZero (⌊m⌋₊ / 2) := ⟨h⟩; ofGroup (DihedralGroup (⌊m⌋₊ / 2))
def kleinFour : Grp := ofGroup (Multiplicative (ZMod 2 × ZMod 2))
def prod (G H : Grp) : Grp := letI := G.2; letI := H.2; ofGroup (Fin G.1 × Fin H.1)

end

end Leanify.Groups
