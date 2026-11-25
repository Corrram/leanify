import Leanify.Library.Core

/-! # Vocabulary: simple Lie algebras

Dimensions, ranks, roots and Coxeter numbers of the complex simple Lie algebras by their type
(`We write $d(n)$ for the dimension of the special linear Lie algebra of rank $n$.`).

* notions: the dimensions `n² + 2n` of `A_n = sl_{n+1}`, `n(2n+1)` of `B_n = so_{2n+1}` and
  `C_n = sp_{2n}`, `n(2n-1)` of `D_n = so_{2n}`; the numbers of positive roots `n(n+1)/2`, `n²`,
  `n²` and `n(n-1)`; the Coxeter numbers `n+1`, `2n`, `2n` and `2n-2`. (The relation
  `dim = rank · (Coxeter number + 1)` holds for each.)

Every meaning is a term of the core language. -/

namespace Leanify.LieAlgebras
open Build Core

def rank (k : Nat) (n : B) : B := and (isInt n) (le (num k) n)
def series (name : Phrase) (k : Nat) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real (rank k)], doc, value := close <| lamT .real (rank k) body }

def vocab : Vocab where
  notions := [
    series phrase!"dimension of the special linear Lie algebra of rank $v$" 1 (fun n => add (mul n n) (mul (num 2) n)) "`n² + 2n` (`A_n`)",
    series phrase!"dimension of the odd orthogonal Lie algebra of rank $v$" 2 (fun n => mul n (add (mul (num 2) n) (num 1))) "`n(2n+1)` (`B_n`)",
    series phrase!"dimension of the symplectic Lie algebra of rank $v$" 3 (fun n => mul n (add (mul (num 2) n) (num 1))) "`n(2n+1)` (`C_n`)",
    series phrase!"dimension of the even orthogonal Lie algebra of rank $v$" 4 (fun n => mul n (sub (mul (num 2) n) (num 1))) "`n(2n-1)` (`D_n`)",
    series phrase!"number of positive roots of the special linear Lie algebra of rank $v$" 1 (fun n => div (mul n (add n (num 1))) (num 2)) "`n(n+1)/2`",
    series phrase!"number of positive roots of the odd orthogonal Lie algebra of rank $v$" 2 (fun n => mul n n) "`n²`",
    series phrase!"number of positive roots of the symplectic Lie algebra of rank $v$" 3 (fun n => mul n n) "`n²`",
    series phrase!"number of positive roots of the even orthogonal Lie algebra of rank $v$" 4 (fun n => mul n (sub n (num 1))) "`n(n-1)`",
    series phrase!"Coxeter number of the special linear Lie algebra of rank $v$" 1 (fun n => add n (num 1)) "`n+1`",
    series phrase!"Coxeter number of the odd orthogonal Lie algebra of rank $v$" 2 (fun n => mul (num 2) n) "`2n`",
    series phrase!"Coxeter number of the symplectic Lie algebra of rank $v$" 3 (fun n => mul (num 2) n) "`2n`",
    series phrase!"Coxeter number of the even orthogonal Lie algebra of rank $v$" 4 (fun n => sub (mul (num 2) n) (num 2)) "`2n-2`"]


end Leanify.LieAlgebras
