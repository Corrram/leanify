import Leanify.Library.Numbers

/-! # Vocabulary: finite fields and linear algebra over them

Counts over the field with `q` elements, `q` a prime power (`We write $g(n,q)$ for the order of
the general linear group of degree $n$ over the field with $q$ elements.`).

* nouns and modifiers: `prime power` (`p^k` for a prime `p` and `k ≥ 1`).
* notions: the orders of `GL_n(F_q)` and of `SL_n(F_q)`; the number of square matrices of order
  `n`; the number of `k`-dimensional subspaces of `F_q^n`; the number of points of the projective
  space of dimension `n`; the number of primitive elements of `F_q`.

The counts are constants, interpreted by the declarations of
`Leanify/Library/FiniteFieldsModel.lean`: over Mathlib's `GaloisField p k` for `q = p^k`, the
number of elements of `Matrix.GeneralLinearGroup`, `Matrix.SpecialLinearGroup`, `Matrix`, of the
subspaces of `Fin n → F_q` of dimension `k` (`Submodule`, `Module.finrank`), of
`Projectivization`, and of the generators of the multiplicative group. Their closed forms
(`∏_{k=0}^{n-1}(q^n - q^k)`, the Gaussian binomial coefficient, `(q^{n+1} - 1)/(q - 1)`,
`φ(q-1)`) are theorems, not definitions. -/

namespace Leanify.FiniteFields
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def primePower (q : B) : B := exR fun p => and (Numbers.isPrime p) (exR fun k => and (posInt k) (eq (zpow p k) q))
def primePowerTm : Tm := predR primePower

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def glOrder : Nat := 0
def slOrder : Nat := 1
def squareMatrices : Nat := 2
def subspaces : Nat := 3
def projectivePoints : Nat := 4
def primitiveElements : Nat := 5
end Const

/-- A count of a number and the order `q` of the field, the constant `c`. -/
def overQ (name : Phrase) (d : B → B) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d, dom2 .real fun _ q => primePower q], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\lvert GL_{#1}(\\mathbb{F}_{#2})\\rvert", w!"\\lvert SL_{#1}(\\mathbb{F}_{#2})\\rvert",
    w!"\\lvert M_{#1}(\\mathbb{F}_{#2})\\rvert", w!"\\binom{#2}{#1}_{#3}", w!"\\lvert \\mathbb{P}^{#1}(\\mathbb{F}_{#2})\\rvert",
    w!"\\operatorname{prim}"]
  constLean := [w!"Leanify.FiniteFields.glOrder", w!"Leanify.FiniteFields.slOrder", w!"Leanify.FiniteFields.squareMatrices",
    w!"Leanify.FiniteFields.subspaces", w!"Leanify.FiniteFields.projectivePoints", w!"Leanify.FiniteFields.primitiveElements"]
  modules := [w!"Leanify.Library.FiniteFieldsModel"]
  nouns := [noun phrase!"prime power" phrase!"prime powers" primePowerTm "`p^k` for a prime `p` and an integer `k ≥ 1`"]
  mods := [{ phrase := phrase!"prime power", prenominal := false, ty := .real, pred := primePowerTm,
             doc := "`p^k` for a prime `p` and an integer `k ≥ 1`" }]
  notions := [
    overQ phrase!"order of the general linear group of degree $v$ over the field with $v$ elements" posInt Const.glOrder
      "the invertible matrices of order `n` over Mathlib `GaloisField p k`, `q = p^k` (`∏_{k=0}^{n-1}(q^n - q^k)`)",
    overQ phrase!"order of the special linear group of degree $v$ over the field with $v$ elements" posInt Const.slOrder
      "the matrices of determinant `1` (Mathlib `Matrix.SpecialLinearGroup`; `|GL_n(F_q)|/(q-1)`)",
    overQ phrase!"number of square matrices of order $v$ over the field with $v$ elements" natP Const.squareMatrices
      "the matrices `Fin n × Fin n` over `F_q` (`q^{n²}`)",
    { name := phrase!"number of $v$-dimensional subspaces of a space of dimension $v$ over the field with $v$ elements",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ n => natP n, dom3 .real fun _ _ q => primePower q],
      doc := "the subspaces of `Fin n → F_q` of dimension `k` (the Gaussian binomial coefficient `∏_{i=0}^{k-1}(q^{n-i} - 1)/(q^{i+1} - 1)` for `k ≤ n`)",
      value := .const Const.subspaces },
    overQ phrase!"number of points of the projective space of dimension $v$ over the field with $v$ elements" natP
      Const.projectivePoints "the lines of `Fin (n+1) → F_q` (Mathlib `Projectivization`; `(q^{n+1} - 1)/(q - 1)`)",
    { name := phrase!"number of primitive elements of the field with $v$ elements", ty := .real ⟶ .real, doms := [dom1 .real primePower],
      doc := "the generators of the multiplicative group of `F_q` (`φ(q - 1)`)",
      value := .const Const.primitiveElements }]

end Leanify.FiniteFields
