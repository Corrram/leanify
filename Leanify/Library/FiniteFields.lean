import Leanify.Library.Numbers

/-! # Vocabulary: finite fields and linear algebra over them

Counts over the field with `q` elements, `q` a prime power (`We write $g(n,q)$ for the order of
the general linear group of degree $n$ over the field with $q$ elements.`).

* nouns and modifiers: `prime power` (`p^k` for a prime `p` and `k ≥ 1`).
* notions: the order `∏_{k=0}^{n-1}(q^n - q^k)` of `GL_n(F_q)` and `|GL_n(F_q)|/(q-1)` of
  `SL_n(F_q)`; the number `q^{n²}` of square matrices; the number of `k`-dimensional subspaces of
  `F_q^n` (the Gaussian binomial coefficient `∏_{i=0}^{k-1}(q^{n-i} - 1)/(q^{i+1} - 1)`); the
  number `(q^{n+1} - 1)/(q - 1)` of points of the projective space of dimension `n`; the number
  `φ(q-1)` of primitive elements of `F_q`.

Every meaning is a term of the core language. -/

namespace Leanify.FiniteFields
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def finProd (a b : B) (body : B → B) : B := app (app (app (prim .finProd) a) b) (lamR body)
def primePower (q : B) : B := exR fun p => and (Numbers.isPrime p) (exR fun k => and (posInt k) (eq (zpow p k) q))
def primePowerTm : Tm := predR primePower
def coprime (a b : B) : B := allR fun d => imp (and (posInt d) (and (divides d a) (divides d b))) (eq d (num 1))
def totient (n : B) : B := finSum (num 1) n fun k => cases (coprime k n) (num 1) (num 0)
def gl (n q : B) : B := finProd (num 0) (sub n (num 1)) fun k => sub (zpow q n) (zpow q k)
def overQ (name : Phrase) (d : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d, dom2 .real fun _ q => primePower q], doc,
    value := close <| lamT .real d fun n => lamT .real primePower fun q => body n q }

def vocab : Vocab where
  nouns := [noun phrase!"prime power" phrase!"prime powers" primePowerTm "`p^k` for a prime `p` and an integer `k ≥ 1`"]
  mods := [{ phrase := phrase!"prime power", prenominal := false, ty := .real, pred := primePowerTm,
             doc := "`p^k` for a prime `p` and an integer `k ≥ 1`" }]
  notions := [
    overQ phrase!"order of the general linear group of degree $v$ over the field with $v$ elements" posInt gl
      "`∏_{k=0}^{n-1}(q^n - q^k)`",
    overQ phrase!"order of the special linear group of degree $v$ over the field with $v$ elements" posInt
      (fun n q => div (gl n q) (sub q (num 1))) "`|GL_n(F_q)|/(q-1)`",
    overQ phrase!"number of square matrices of order $v$ over the field with $v$ elements" natP
      (fun n q => zpow q (mul n n)) "`q^{n²}`",
    { name := phrase!"number of $v$-dimensional subspaces of a space of dimension $v$ over the field with $v$ elements",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun k n => and (natP n) (le k n), dom3 .real fun _ _ q => primePower q],
      doc := "the Gaussian binomial coefficient `∏_{i=0}^{k-1}(q^{n-i} - 1)/(q^{i+1} - 1)`",
      value := close <| lamT .real natP fun k => lamT .real (fun n => and (natP n) (le k n)) fun n => lamT .real primePower fun q =>
        finProd (num 0) (sub k (num 1)) fun i => div (sub (zpow q (sub n i)) (num 1)) (sub (zpow q (add i (num 1))) (num 1)) },
    overQ phrase!"number of points of the projective space of dimension $v$ over the field with $v$ elements" natP
      (fun n q => div (sub (zpow q (add n (num 1))) (num 1)) (sub q (num 1))) "`(q^{n+1} - 1)/(q - 1)`",
    { name := phrase!"number of primitive elements of the field with $v$ elements", ty := .real ⟶ .real, doms := [dom1 .real primePower],
      doc := "`φ(q - 1)`: the generators of the multiplicative group",
      value := close <| lamT .real primePower fun q => totient (sub q (num 1)) }]

end Leanify.FiniteFields
