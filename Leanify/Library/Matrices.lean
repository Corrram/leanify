import Leanify.Library.Core

/-! # Vocabulary: matrices

A matrix is a real `m × n` matrix, for some `m` and `n`: a type of its own (Mathlib's
`Matrix (Fin m) (Fin n) ℝ`), so that an article binds matrices as it binds numbers
(`Let $A$ be an $n\times n$ matrix.`) and writes their algebra: `A+B` and `A-B` (of the same
size), `AB` (when the columns of `A` are as many as the rows of `B`), `cA` for a number `c`,
`A^k` (of a square matrix, `k` natural), `A^{-1}` and `A/B` (of an invertible matrix),
`A^\top` (also `A^T`), `\det A`, `\operatorname{tr} A` and `\operatorname{rank} A`. A real number
is the `1 × 1` matrix: the product of such a matrix with another is the scalar multiple.

* nouns: `matrix`, `real matrix`, `square matrix`;
* adjectives: `square`, `symmetric`, `skew-symmetric`, `orthogonal`, `invertible`,
  `singular`, `nonsingular`, `positive definite`, `positive semidefinite`, `diagonal`,
  `upper triangular`, `lower triangular`, `nilpotent`, `idempotent`, `stochastic`,
  `$m\times n$`, `of size $m\times n$`, `of rank $r$`;
* notions: the numbers of rows and columns, the entry in row `i` and column `j`, the
  determinant, trace, rank, transpose and inverse, the identity and zero matrices, the
  characteristic polynomial (a real function, `t ↦ det(tI - A)`), the set of (real)
  eigenvalues, and the set of the `m × n` matrices.

The constants are interpreted by `Leanify/Library/MatricesModel.lean`. -/

namespace Leanify.Matrices
open Build Core

/-- Matrices: the field's base type. -/
abbrev M : Ty := .base 0

namespace Const
def rows : Nat := 0
def cols : Nat := 1
def ofReal : Nat := 2
def square : Nat := 3
def sameSize : Nat := 4
def mulable : Nat := 5
def add : Nat := 6
def sub : Nat := 7
def neg : Nat := 8
def mul : Nat := 9
def pow : Nat := 10
def inverse : Nat := 11
def transpose : Nat := 12
def div : Nat := 13
def det : Nat := 14
def trace : Nat := 15
def rank : Nat := 16
def invertible : Nat := 17
def divisible : Nat := 18
def entry : Nat := 19
def isEntry : Nat := 20
def identity : Nat := 21
def zero : Nat := 22
def charpoly : Nat := 23
def eigenvalue : Nat := 24
def symmetric : Nat := 25
def skewSymmetric : Nat := 26
def orthogonal : Nat := 27
def posDef : Nat := 28
def posSemidef : Nat := 29
def diagonal : Nat := 30
def upper : Nat := 31
def lower : Nat := 32
def nilpotent : Nat := 33
def idempotent : Nat := 34
def stochastic : Nat := 35
end Const
open Const

def mPred (p : B → B) : Tm := close <| lamT M (fun _ => tt) p
def squarePred : Tm := .const square
def sqDom : Option Tm := some squarePred
def natDom : Option Tm := some nonnegInt

def nounM (sing plural : Phrase) (pred : Tm) (doc : String) : Noun := { sing, plural, ty := M, pred, doc }
def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := M, pred, doc }
def ofM (name : Phrase) (value : Tm) (dom : Option Tm) (ty : Ty) (doc : String) : Notion :=
  { name, value, ty, doms := [dom], doc }

/-- An `m × n` matrix. -/
def ofSize : Tm := close <| lamR fun m => lamR fun n => lamT M (fun _ => tt) fun a =>
  and (eq (app (const rows) a) m) (eq (app (const cols) a) n)
def ofSizeSq : Tm := close <| lamR fun n => lamT M (fun _ => tt) fun a =>
  and (eq (app (const rows) a) n) (eq (app (const cols) a) n)

/-- The entry in row `i` and column `j`, for `1 ≤ i ≤ m`, `1 ≤ j ≤ n`. -/
def entryOf : Tm := close <| lamT M (fun _ => tt) fun a => lamR fun i => lamR fun j =>
  guard (app (app (app (const isEntry) a) i) j) (app (app (app (const entry) a) i) j)

def eigenvalues : Tm := close <| lamT M (fun _ => tt) fun a => lamR fun t => app2 (const eigenvalue) a t

def vocab : Vocab where
  types := [w!"\\mathrm{Mat}"]
  consts := [M ⟶ .real, M ⟶ .real, .real ⟶ M, M ⟶ .prop, M ⟶ M ⟶ .prop, M ⟶ M ⟶ .prop,
    M ⟶ M ⟶ M, M ⟶ M ⟶ M, M ⟶ M, M ⟶ M ⟶ M, M ⟶ .real ⟶ M, M ⟶ M, M ⟶ M, M ⟶ M ⟶ M,
    M ⟶ .real, M ⟶ .real, M ⟶ .real, M ⟶ .prop, M ⟶ M ⟶ .prop, M ⟶ .real ⟶ .real ⟶ .real,
    M ⟶ .real ⟶ .real ⟶ .prop, .real ⟶ M, .real ⟶ .real ⟶ M, M ⟶ Ty.rfun, M ⟶ .real ⟶ .prop,
    M ⟶ .prop, M ⟶ .prop, M ⟶ .prop, M ⟶ .prop, M ⟶ .prop, M ⟶ .prop, M ⟶ .prop, M ⟶ .prop,
    M ⟶ .prop, M ⟶ .prop, M ⟶ .prop]
  constNames := [w!"\\operatorname{rows}", w!"\\operatorname{cols}", w!"", w!"\\operatorname{Square}",
    w!"\\operatorname{SameSize}(#1,#2)", w!"\\operatorname{Mulable}(#1,#2)", w!"+", w!"-", w!"-", w!"\\cdot", w!"^",
    w!"#^{-1}", w!"#^{\\top}", w!"/", w!"\\det", w!"\\operatorname{tr}", w!"\\operatorname{rank}",
    w!"\\operatorname{Invertible}", w!"\\operatorname{Divisible}(#1,#2)", w!"#1_{#2,#3}", w!"\\operatorname{IsEntry}",
    w!"I_{#}", w!"0_{#1\\times #2}", w!"\\chi_{#}", w!"\\operatorname{Eigenvalue}",
    w!"\\operatorname{Symmetric}", w!"\\operatorname{SkewSymmetric}", w!"\\operatorname{Orthogonal}",
    w!"\\operatorname{PosDef}", w!"\\operatorname{PosSemidef}", w!"\\operatorname{Diagonal}",
    w!"\\operatorname{UpperTriangular}", w!"\\operatorname{LowerTriangular}", w!"\\operatorname{Nilpotent}",
    w!"\\operatorname{Idempotent}", w!"\\operatorname{Stochastic}"]
  constLean := [w!"Leanify.Matrices.rows", w!"Leanify.Matrices.cols", w!"Leanify.Matrices.ofReal",
    w!"Leanify.Matrices.Square", w!"Leanify.Matrices.SameSize", w!"Leanify.Matrices.Mulable",
    w!"Leanify.Matrices.add", w!"Leanify.Matrices.sub", w!"Leanify.Matrices.neg", w!"Leanify.Matrices.mul",
    w!"Leanify.Matrices.pow", w!"Leanify.Matrices.inverse", w!"Leanify.Matrices.transpose",
    w!"Leanify.Matrices.div", w!"Leanify.Matrices.det", w!"Leanify.Matrices.trace", w!"Leanify.Matrices.rank",
    w!"Leanify.Matrices.Invertible", w!"Leanify.Matrices.Divisible", w!"Leanify.Matrices.entry",
    w!"Leanify.Matrices.IsEntry", w!"Leanify.Matrices.identity", w!"Leanify.Matrices.zero",
    w!"Leanify.Matrices.charpoly", w!"Leanify.Matrices.Eigenvalue", w!"Leanify.Matrices.Symmetric",
    w!"Leanify.Matrices.SkewSymmetric", w!"Leanify.Matrices.Orthogonal", w!"Leanify.Matrices.PosDef",
    w!"Leanify.Matrices.PosSemidef", w!"Leanify.Matrices.Diagonal", w!"Leanify.Matrices.UpperTriangular",
    w!"Leanify.Matrices.LowerTriangular", w!"Leanify.Matrices.Nilpotent", w!"Leanify.Matrices.Idempotent",
    w!"Leanify.Matrices.Stochastic"]
  typeLean := [(w!"Leanify.Matrices.Mat", w!"Leanify.Matrices.Mat.empty")]
  modules := [w!"Leanify.Library.MatricesModel"]
  nouns := [
    nounM phrase!"matrix" phrase!"matrices" (mPred fun _ => tt) "a real `m × n` matrix (Mathlib `Matrix (Fin m) (Fin n) ℝ`)",
    nounM phrase!"real matrix" phrase!"real matrices" (mPred fun _ => tt) "(Mathlib `Matrix (Fin m) (Fin n) ℝ`)",
    nounM phrase!"square matrix" phrase!"square matrices" squarePred "an `n × n` matrix"]
  mods := [
    mod phrase!"square" true squarePred "`n × n`",
    mod phrase!"real" true (mPred fun _ => tt) "a matrix of real numbers (every matrix is)",
    mod phrase!"symmetric" true (.const symmetric) "`Aᵀ = A` (Mathlib `Matrix.IsSymm`)",
    mod phrase!"skew-symmetric" true (.const skewSymmetric) "`Aᵀ = -A`",
    mod phrase!"orthogonal" true (.const orthogonal) "`AᵀA = I`",
    mod phrase!"invertible" true (.const invertible) "square, with `det A ≠ 0`",
    mod phrase!"nonsingular" true (.const invertible) "square, with `det A ≠ 0`",
    mod phrase!"singular" true (mPred fun a => and (app (const square) a) (eq (app (const det) a) (num 0)))
      "square, with `det A = 0`",
    mod phrase!"positive definite" true (.const posDef) "`xᵀAx > 0` for `x ≠ 0`, and symmetric (Mathlib `Matrix.PosDef`)",
    mod phrase!"positive semidefinite" true (.const posSemidef) "`xᵀAx ≥ 0`, and symmetric (Mathlib `Matrix.PosSemidef`)",
    mod phrase!"diagonal" true (.const diagonal) "square, zero off the diagonal",
    mod phrase!"upper triangular" true (.const upper) "square, zero below the diagonal",
    mod phrase!"lower triangular" true (.const lower) "square, zero above the diagonal",
    mod phrase!"nilpotent" true (.const nilpotent) "square, `A^k = 0` for some `k` (Mathlib `IsNilpotent`)",
    mod phrase!"idempotent" true (.const idempotent) "square, `A² = A`",
    mod phrase!"stochastic" true (.const stochastic) "square, nonnegative entries, rows summing to `1`",
    mod phrase!"$v\\times v$" true ofSize "of size `m × n`",
    mod phrase!"of size $v\\times v$" false ofSize "`m × n`",
    mod phrase!"of order $v$" false ofSizeSq "`n × n`",
    mod phrase!"of rank $v$" false (close <| lamR fun r => lamT M (fun _ => tt) fun a => eq (app (const rank) a) r)
      "(Mathlib `Matrix.rank`)"]
  notions := [
    ofM phrase!"number of rows of $v$" (.const rows) none (M ⟶ .real) "`m`",
    ofM phrase!"number of columns of $v$" (.const cols) none (M ⟶ .real) "`n`",
    { name := phrase!"entry of $v$ in row $v$ and column $v$", value := entryOf, ty := M ⟶ .real ⟶ .real ⟶ .real,
      doc := "`A i j`, for `1 ≤ i ≤ m`, `1 ≤ j ≤ n`" },
    ofM phrase!"determinant of $v$" (.const det) sqDom (M ⟶ .real) "of a square matrix (Mathlib `Matrix.det`)",
    ofM phrase!"trace of $v$" (.const trace) sqDom (M ⟶ .real) "of a square matrix (Mathlib `Matrix.trace`)",
    ofM phrase!"rank of $v$" (.const rank) none (M ⟶ .real) "(Mathlib `Matrix.rank`)",
    ofM phrase!"transpose of $v$" (.const transpose) none (M ⟶ M) "`Aᵀ`",
    ofM phrase!"inverse of $v$" (.const inverse) (some (.const invertible)) (M ⟶ M)
      "of an invertible matrix (Mathlib `Matrix.inv`)",
    ofM phrase!"identity matrix of size $v$" (.const identity) natDom (.real ⟶ M) "`I_n`",
    ofM phrase!"identity matrix of order $v$" (.const identity) natDom (.real ⟶ M) "`I_n`",
    { name := phrase!"$v\\times v$ identity matrix", ty := .real ⟶ .real ⟶ M, doms := [natDom, natDom],
      value := close <| lamR fun m => lamR fun n => guard (eq m n) (app (const identity) n), doc := "`I_n`" },
    { name := phrase!"$v\\times v$ zero matrix", value := .const zero, ty := .real ⟶ .real ⟶ M,
      doms := [natDom, natDom], doc := "the `m × n` matrix of zeros" },
    { name := phrase!"zero matrix of size $v\\times v$", value := .const zero, ty := .real ⟶ .real ⟶ M,
      doms := [natDom, natDom], doc := "the `m × n` matrix of zeros" },
    ofM phrase!"characteristic polynomial of $v$" (.const charpoly) sqDom (M ⟶ Ty.rfun)
      "`t ↦ det(tI - A)` (Mathlib `Matrix.charpoly`)",
    ofM phrase!"set of eigenvalues of $v$" eigenvalues sqDom (M ⟶ .real ⟶ .prop)
      "the real `λ` with `Av = λv` for some `v ≠ 0`",
    { name := phrase!"set of $v\\times v$ matrices", value := ofSize, ty := .real ⟶ .real ⟶ M ⟶ .prop,
      doms := [natDom, natDom], doc := "`M_{m×n}(ℝ)`" },
    { name := phrase!"set of real $v\\times v$ matrices", value := ofSize, ty := .real ⟶ .real ⟶ M ⟶ .prop,
      doms := [natDom, natDom], doc := "`M_{m×n}(ℝ)`" }]
  methods := [
    { ty := M, op := .ofReal, const := ofReal, doc := "a real number `c` as the `1 × 1` matrix `(c)`" },
    { ty := M, op := .add, const := add, doc := "`A + B`, of the same size", dom := some (.const sameSize) },
    { ty := M, op := .sub, const := sub, doc := "`A - B`, of the same size", dom := some (.const sameSize) },
    { ty := M, op := .neg, const := neg, doc := "`-A`" },
    { ty := M, op := .mul, const := mul, doc := "`AB` (`cA` for a `1 × 1` matrix `c`)", dom := some (.const mulable) },
    { ty := M, op := .div, const := div, doc := "`A B⁻¹`, for an invertible `B` (`1/A = A⁻¹`)",
      dom := some (.const divisible) },
    { ty := M, op := .pow, const := pow, doc := "`A^k` of a square matrix, `k` natural",
      dom := some (close <| lamT M (fun _ => tt) fun a => lamR fun _ => app (const square) a) },
    { ty := M, op := .decor w!"^\\top", const := transpose, doc := "`Aᵀ` (also `A^T`, `A^\\intercal`)" },
    { ty := M, op := .fn w!"\\det", const := det, doc := "the determinant of a square matrix", dom := sqDom },
    { ty := M, op := .fn w!"det", const := det, doc := "the determinant of a square matrix", dom := sqDom },
    { ty := M, op := .fn w!"tr", const := trace, doc := "the trace of a square matrix", dom := sqDom },
    { ty := M, op := .fn w!"rank", const := rank, doc := "the rank (Mathlib `Matrix.rank`)" },
    { ty := M, op := .fn w!"rk", const := rank, doc := "the rank (Mathlib `Matrix.rank`)" }]

end Leanify.Matrices
