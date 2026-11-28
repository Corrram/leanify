import Leanify.Denote
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # The meaning of the field `matrices`

A matrix is a real `m × n` matrix, for some `m` and `n` (Mathlib's
`Matrix (Fin m) (Fin n) ℝ`); its entry in row `i` and column `j` is at `(i - 1, j - 1)`. A real
number `c` is the `1 × 1` matrix `(c)`, and the product of a `1 × 1` matrix with a matrix of
another shape is the scalar multiple (the Kronecker product), so that `cA` is the scalar
multiple and `1/A` the inverse. -/

namespace Leanify.Matrices
open Matrix

/-- A real matrix of some size `m × n`. -/
def Mat : Type := Σ m : ℕ, Σ n : ℕ, Matrix (Fin m) (Fin n) ℝ

/-- The `0 × 0` matrix. -/
def Mat.empty : Mat := ⟨0, 0, 0⟩

noncomputable section
open Classical

def rows (A : Mat) : ℝ := A.1
def cols (A : Mat) : ℝ := A.2.1

/-- `(c)`, a real number as a `1 × 1` matrix. -/
def ofReal (c : ℝ) : Mat := ⟨1, 1, fun _ _ => c⟩

def IsScalar (A : Mat) : Prop := A.1 = 1 ∧ A.2.1 = 1
def Square (A : Mat) : Prop := A.1 = A.2.1
def SameSize (A B : Mat) : Prop := A.1 = B.1 ∧ A.2.1 = B.2.1
/-- `AB` is defined: the columns of `A` are as many as the rows of `B`, or one is `1 × 1`. -/
def Mulable (A B : Mat) : Prop := A.2.1 = B.1 ∨ IsScalar A ∨ IsScalar B

/-- The entry of `A` at `(i, j)` (`0` outside). -/
def at' (A : Mat) (i j : ℕ) : ℝ := if h : i < A.1 ∧ j < A.2.1 then A.2.2 ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- A matrix of the size `m × n` with the entries `f i j`. -/
def mk (m n : ℕ) (f : ℕ → ℕ → ℝ) : Mat := ⟨m, n, fun i j => f i j⟩

def add (A B : Mat) : Mat := mk A.1 A.2.1 fun i j => at' A i j + at' B i j
def sub (A B : Mat) : Mat := mk A.1 A.2.1 fun i j => at' A i j - at' B i j
def neg (A : Mat) : Mat := mk A.1 A.2.1 fun i j => -at' A i j
def smul (c : ℝ) (A : Mat) : Mat := mk A.1 A.2.1 fun i j => c * at' A i j

def mul (A B : Mat) : Mat :=
  if A.2.1 = B.1 then mk A.1 B.2.1 fun i k => ∑ j ∈ Finset.range A.2.1, at' A i j * at' B j k
  else if IsScalar A then smul (at' A 0 0) B
  else if IsScalar B then smul (at' B 0 0) A
  else A

/-- A square matrix as a `Matrix (Fin n) (Fin n) ℝ`. -/
def sq (A : Mat) : Matrix (Fin A.1) (Fin A.1) ℝ := fun i j => at' A i j

def ofSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Mat := ⟨n, n, M⟩

def pow (A : Mat) (k : ℝ) : Mat := ofSq (sq A ^ ⌊k⌋₊)
def inverse (A : Mat) : Mat := ofSq (sq A)⁻¹
def transpose (A : Mat) : Mat := ⟨A.2.1, A.1, A.2.2ᵀ⟩

/-- `A / B = A B⁻¹`. -/
def div (A B : Mat) : Mat := mul A (inverse B)

def det (A : Mat) : ℝ := (sq A).det
def trace (A : Mat) : ℝ := (sq A).trace
def rank (A : Mat) : ℝ := A.2.2.rank
/-- The dimension of the null space `{x : Ax = 0}` of `A`. -/
def nullity (A : Mat) : ℝ := (Module.finrank ℝ (LinearMap.ker A.2.2.mulVecLin) : ℝ)

def Invertible (A : Mat) : Prop := Square A ∧ (sq A).det ≠ 0
/-- `A / B` is defined: `B` is invertible and `A B⁻¹` is defined. -/
def Divisible (A B : Mat) : Prop := Invertible B ∧ Mulable A (inverse B)

/-- The entry in row `i` and column `j` (from `1`). -/
def entry (A : Mat) (i j : ℝ) : ℝ := at' A (⌊i⌋₊ - 1) (⌊j⌋₊ - 1)
def IsEntry (A : Mat) (i j : ℝ) : Prop :=
  ∃ a b : ℕ, (a : ℝ) = i ∧ (b : ℝ) = j ∧ 1 ≤ a ∧ a ≤ A.1 ∧ 1 ≤ b ∧ b ≤ A.2.1

def identity (n : ℝ) : Mat := ofSq (1 : Matrix (Fin ⌊n⌋₊) (Fin ⌊n⌋₊) ℝ)
def zero (m n : ℝ) : Mat := ⟨⌊m⌋₊, ⌊n⌋₊, 0⟩

/-- The characteristic polynomial `t ↦ det(tI - A)`. -/
def charpoly (A : Mat) : ℝ → ℝ := fun t => (sq A).charpoly.eval t

/-- The real eigenvalues. -/
def Eigenvalue (A : Mat) (μ : ℝ) : Prop := ∃ v : Fin A.1 → ℝ, v ≠ 0 ∧ (sq A).mulVec v = μ • v

/-- `v` is an eigenvector of `A`: a nonzero `n × 1` matrix, for `A` of size `n × n`, with
`Av = λv` for a real `λ`. -/
def Eigenvector (A v : Mat) : Prop :=
  Square A ∧ v.1 = A.1 ∧ v.2.1 = 1 ∧ (∃ i : Fin A.1, at' v i 0 ≠ 0) ∧
    ∃ μ : ℝ, (sq A).mulVec (fun i : Fin A.1 => at' v i 0) = μ • (fun i : Fin A.1 => at' v i 0)

def Symmetric (A : Mat) : Prop := Square A ∧ (sq A).IsSymm
def SkewSymmetric (A : Mat) : Prop := Square A ∧ (sq A)ᵀ = -sq A
def Orthogonal (A : Mat) : Prop := Square A ∧ (sq A)ᵀ * sq A = 1
def PosDef (A : Mat) : Prop := Square A ∧ (sq A).PosDef
def PosSemidef (A : Mat) : Prop := Square A ∧ (sq A).PosSemidef
/-- The square root of a positive semidefinite matrix: the positive semidefinite `B` with
`BB = A` (there is exactly one: Mathlib's `CFC.sqrt` of the matrix), and the `0 × 0` matrix
if there is none. -/
def sqrt (A : Mat) : Mat :=
  if h : ∃ B : Mat, PosSemidef B ∧ mul B B = A then Classical.choose h else Mat.empty
def Diagonal (A : Mat) : Prop := Square A ∧ ∀ i j, i ≠ j → at' A i j = 0
def UpperTriangular (A : Mat) : Prop := Square A ∧ ∀ i j, j < i → at' A i j = 0
def LowerTriangular (A : Mat) : Prop := Square A ∧ ∀ i j, i < j → at' A i j = 0
def Nilpotent (A : Mat) : Prop := Square A ∧ IsNilpotent (sq A)
def Idempotent (A : Mat) : Prop := Square A ∧ sq A * sq A = sq A
/-- Nonnegative entries, and each row sums to `1`. -/
def Stochastic (A : Mat) : Prop :=
  Square A ∧ (∀ i j, 0 ≤ at' A i j) ∧ ∀ i < A.1, ∑ j ∈ Finset.range A.2.1, at' A i j = 1

/-- `B` is similar to `A`: square matrices of the same size with `B = P⁻¹AP` for an invertible
`P`. -/
def Similar (A B : Mat) : Prop :=
  Square A ∧ SameSize A B ∧ ∃ P : Matrix (Fin A.1) (Fin A.1) ℝ, P.det ≠ 0 ∧ ∀ i j : Fin A.1,
    at' B i j = (P⁻¹ * sq A * P) i j
/-- Diagonalizable over the real numbers: `P⁻¹AP` is diagonal for an invertible real `P`. -/
def Diagonalizable (A : Mat) : Prop :=
  Square A ∧ ∃ P : Matrix (Fin A.1) (Fin A.1) ℝ, P.det ≠ 0 ∧ ∀ i j : Fin A.1, i ≠ j → (P⁻¹ * sq A * P) i j = 0
/-- Orthogonally diagonalizable: `QᵀAQ` is diagonal for an orthogonal `Q`. -/
def OrthDiagonalizable (A : Mat) : Prop :=
  Square A ∧ ∃ Q : Matrix (Fin A.1) (Fin A.1) ℝ, Qᵀ * Q = 1 ∧ ∀ i j : Fin A.1, i ≠ j → (Qᵀ * sq A * Q) i j = 0

end

end Leanify.Matrices
