import Leanify.Denote
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

/-! # The meaning of the field `permutations`

A permutation is a permutation of `Fin n`, for some `n` (its degree); its point `i` is the
number `i + 1`, so that a permutation of degree `n` permutes `1, …, n`. -/

namespace Leanify.Permutations

/-- A permutation of `{1, …, n}`, for some `n`. -/
def Perm : Type := Σ n : ℕ, Equiv.Perm (Fin n)

/-- The permutation of the empty set. -/
def Perm.empty : Perm := ⟨0, 1⟩

noncomputable section
open Classical

/-- The degree `n` of a permutation of `{1, …, n}`. -/
def degree (σ : Perm) : ℝ := σ.1

/-- `i` is one of `1, …, n`. -/
def IsPoint (σ : Perm) (i : ℝ) : Prop := ∃ j : Fin σ.1, (j : ℝ) + 1 = i

/-- `σ(i)` (and `i` for a number that is not a point). -/
def apply (σ : Perm) (i : ℝ) : ℝ :=
  if h : ∃ j : Fin σ.1, (j : ℝ) + 1 = i then ((σ.2 h.choose : Fin σ.1) : ℝ) + 1 else i

/-- `στ = σ ∘ τ`, for permutations of the same degree (`σ` otherwise). -/
def mul (σ τ : Perm) : Perm := if h : τ.1 = σ.1 then ⟨σ.1, σ.2 * (h ▸ τ.2)⟩ else σ

/-- Two permutations of the same degree. -/
def SameDegree (σ τ : Perm) : Prop := σ.1 = τ.1

/-- `σ^k` for a natural number `k`. -/
def pow (σ : Perm) (k : ℝ) : Perm := ⟨σ.1, σ.2 ^ ⌊k⌋₊⟩

def inverse (σ : Perm) : Perm := ⟨σ.1, σ.2⁻¹⟩

def identity (n : ℝ) : Perm := ⟨⌊n⌋₊, 1⟩

def IsIdentity (σ : Perm) : Prop := σ.2 = 1

/-- The sign, `1` or `-1`. -/
def sign (σ : Perm) : ℝ := ((Equiv.Perm.sign σ.2 : ℤ) : ℝ)

def order (σ : Perm) : ℝ := orderOf σ.2

def numFixed (σ : Perm) : ℝ := Fintype.card {i : Fin σ.1 // σ.2 i = i}

/-- The number of cycles, fixed points included. -/
def numCycles (σ : Perm) : ℝ := σ.2.cycleType.card + Fintype.card {i : Fin σ.1 // σ.2 i = i}

def numInversions (σ : Perm) : ℝ := Fintype.card {p : Fin σ.1 × Fin σ.1 // p.1 < p.2 ∧ σ.2 p.2 < σ.2 p.1}

def IsTransposition (σ : Perm) : Prop := σ.2.IsSwap
def IsCycle (σ : Perm) : Prop := σ.2.IsCycle
def IsDerangement (σ : Perm) : Prop := ∀ i, σ.2 i ≠ i
def IsInvolution (σ : Perm) : Prop := σ.2 * σ.2 = 1

end

end Leanify.Permutations
