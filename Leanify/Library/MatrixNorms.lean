import Leanify.Library.Matrices

/-! # Vocabulary: norms, conditioning and structure of matrices

Numerical linear algebra on the real matrices of the field `matrices`, which this field
includes: matrix norms, condition numbers, and the structure that iterative solvers and
factorizations ask for (`Let $A$ be a strictly diagonally dominant matrix.`).

* notions: the Frobenius norm, the maximum absolute row sum (`‖A‖_∞`) and column sum
  (`‖A‖_1`), the condition numbers in these norms (of an invertible matrix), the
  diagonal part;
* adjectives of square matrices: `strictly diagonally dominant`, `diagonally dominant`,
  `tridiagonal`, `upper Hessenberg`, `with bandwidth $k$`, `nonnegative`.

Every meaning is a term of the core language with the constants of `matrices` (sizes,
entries, the inverse): a norm is a finite sum, a maximum over the rows is the description
of a value that some row attains and no row exceeds. -/

namespace Leanify.MatrixNorms
open Build Core
open Leanify.Matrices (M)

def rows (a : B) : B := app (const Matrices.Const.rows) a
def cols (a : B) : B := app (const Matrices.Const.cols) a
def entry (a i j : B) : B := app (app (app (const Matrices.Const.entry) a) i) j
def inv (a : B) : B := app (const Matrices.Const.inverse) a
def invertible (a : B) : B := app (const Matrices.Const.invertible) a
def square (a : B) : B := app (const Matrices.Const.square) a
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def inRange (i n : B) : B := and (isInt i) (and (le (num 1) i) (le i n))
def frob (a : B) : B := sqrt (finSum (num 1) (rows a) fun i => finSum (num 1) (cols a) fun j => mul (entry a i j) (entry a i j))
def rowSum (a i : B) : B := finSum (num 1) (cols a) fun j => abs (entry a i j)
def colSum (a j : B) : B := finSum (num 1) (rows a) fun i => abs (entry a i j)
/-- The largest value of `g(i)` for `1 ≤ i ≤ n`. -/
def maxOver (n : B) (g : B → B) : B :=
  theR fun m => and (exR fun i => and (inRange i n) (eq (g i) m)) (allR fun i => imp (inRange i n) (le (g i) m))
def normInf (a : B) : B := maxOver (rows a) (rowSum a)
def norm1 (a : B) : B := maxOver (cols a) (colSum a)
/-- `∑_{j ≠ i} |a_ij|`. -/
def offDiag (a i : B) : B := sub (rowSum a i) (abs (entry a i i))
def forRows (a : B) (body : B → B) : B := allR fun i => imp (inRange i (rows a)) (body i)
def forEntries (a : B) (body : B → B → B) : B :=
  allR fun i => allR fun j => imp (and (inRange i (rows a)) (inRange j (cols a))) (body i j)
def nonempty (a : B) : B := and (le (num 1) (rows a)) (le (num 1) (cols a))

def mPred (p : B → B) : Tm := close <| lamT M (fun _ => tt) p
def adj (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := M, pred := mPred body, doc }
def ofM (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := M ⟶ .real, doms := [dom1 M d], doc, value := close <| lamT M d body }

/-- The words of the field itself. -/
def own : Vocab where
  mods := [
    adj phrase!"strictly diagonally dominant" true (fun a => and (square a) (forRows a fun i => lt (offDiag a i) (abs (entry a i i))))
      "square, `|a_ii| > ∑_{j≠i} |a_ij|` in every row",
    adj phrase!"diagonally dominant" true (fun a => and (square a) (forRows a fun i => le (offDiag a i) (abs (entry a i i))))
      "square, `|a_ii| ≥ ∑_{j≠i} |a_ij|` in every row",
    adj phrase!"tridiagonal" true (fun a => and (square a) (forEntries a fun i j => imp (lt (num 1) (abs (sub i j))) (eq (entry a i j) (num 0))))
      "square, `a_ij = 0` for `|i - j| > 1`",
    adj phrase!"upper Hessenberg" true (fun a => and (square a) (forEntries a fun i j => imp (lt (add j (num 1)) i) (eq (entry a i j) (num 0))))
      "square, `a_ij = 0` for `i > j + 1`",
    adj phrase!"entrywise nonnegative" true (fun a => forEntries a fun i j => le (num 0) (entry a i j)) "`a_ij ≥ 0`",
    { phrase := phrase!"with bandwidth $v$", prenominal := false, ty := M,
      pred := close <| lamR fun k => lamT M (fun _ => tt) fun a => forEntries a fun i j => imp (lt k (abs (sub i j))) (eq (entry a i j) (num 0)),
      doc := "`a_ij = 0` for `|i - j| > k`" }]
  notions := [
    ofM phrase!"Frobenius norm of $v$" (fun _ => tt) frob "`√(∑ a_ij²)` (Mathlib `Matrix.frobeniusNorm`)",
    ofM phrase!"maximum absolute row sum of $v$" nonempty normInf "`‖A‖_∞ = max_i ∑_j |a_ij|` (Mathlib `Matrix.linfty_opNorm`)",
    ofM phrase!"maximum absolute column sum of $v$" nonempty norm1 "`‖A‖_1 = max_j ∑_i |a_ij|`",
    ofM phrase!"condition number of $v$ in the Frobenius norm" invertible (fun a => mul (frob a) (frob (inv a)))
      "`‖A‖_F ‖A⁻¹‖_F`, of an invertible matrix",
    ofM phrase!"condition number of $v$ in the maximum norm" (fun a => and (invertible a) (nonempty a))
      (fun a => mul (normInf a) (normInf (inv a))) "`‖A‖_∞ ‖A⁻¹‖_∞`, of an invertible matrix",
    ofM phrase!"condition number of $v$ in the column sum norm" (fun a => and (invertible a) (nonempty a))
      (fun a => mul (norm1 a) (norm1 (inv a))) "`‖A‖_1 ‖A⁻¹‖_1`, of an invertible matrix"]

/-- `matrices` with these words: one vocabulary, so that the words of this field use the type
and the constants of `matrices` as they are numbered there. -/
def vocab : Vocab :=
  let G := Vocab.tag w!"matrices" Matrices.vocab
  let O := Vocab.tag w!"matrixnorms" own
  { G with mods := G.mods ++ O.mods, notions := G.notions ++ O.notions }

end Leanify.MatrixNorms
