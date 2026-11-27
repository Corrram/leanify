import Leanify.Library.Core

/-! # Vocabulary: classical orthogonal polynomials

The Legendre, Hermite, Laguerre and Chebyshev polynomials of degree `n`, each a real
function (`We write $P_n$ for the Legendre polynomial of degree $n$.`, then `P_n(x)`).

* `Legendre polynomial of degree $n$`: Mathlib's shifted Legendre polynomial
  `Polynomial.shiftedLegendre n` at `(1 - x)/2` (`∑_{k=0}^{n} \binom{n}{k}² ((x-1)/2)^{n-k} ((x+1)/2)^k`);
* `Hermite polynomial of degree $n$` (the physicists'): `n! ∑_{m=0}^{⌊n/2⌋} (-1)^m (2x)^{n-2m}/(m!(n-2m)!)`;
* `probabilists' Hermite polynomial of degree $n$`: Mathlib's `Polynomial.hermite n`
  (`n! ∑_{m} (-1)^m x^{n-2m}/(2^m m!(n-2m)!)`);
* `Laguerre polynomial of degree $n$`: `∑_{k=0}^{n} \binom{n}{k} (-x)^k/k!`;
* `Chebyshev polynomial of the first kind of degree $n$`: Mathlib's `Polynomial.Chebyshev.T`
  (`∑_{k=0}^{⌊n/2⌋} \binom{n}{2k} (x²-1)^k x^{n-2k}`);
* `Chebyshev polynomial of the second kind of degree $n$`: Mathlib's `Polynomial.Chebyshev.U`
  (`∑_{k=0}^{⌊n/2⌋} \binom{n+1}{2k+1} (x²-1)^k x^{n-2k}`).

The physicists' Hermite and the Laguerre polynomials are their explicit sums, terms of the core
language; the others are constants, interpreted by the declarations of
`Leanify/Library/OrthogonalPolynomialsModel.lean` with Mathlib's polynomials (whose explicit
sums are theorems), for a degree `n ≥ 0`. -/

namespace Leanify.OrthogonalPolynomials
open Build Core

abbrev F : Ty := Ty.rfun

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def half (n : B) : B := floor (div n (num 2))
def sign (m : B) : B := zpow (neg (num 1)) m

def hermite (n x : B) : B :=
  mul (fact n) (finSum (num 0) (half n) fun m =>
    div (mul (sign m) (zpow (mul (num 2) x) (sub n (mul (num 2) m)))) (mul (fact m) (fact (sub n (mul (num 2) m)))))
def laguerre (n x : B) : B := finSum (num 0) n fun k => div (mul (binom n k) (zpow (neg x) k)) (fact k)

def poly (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F, doms := [dom1 .real natP], doc, value := close <| lamT .real natP fun n => lamR fun x => body n x }
/-- A polynomial of Mathlib, the constant `c`. -/
def polyC (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ F, doms := [dom1 .real natP], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ F, .real ⟶ F, .real ⟶ F, .real ⟶ F]
  constNames := [w!"P_{#}", w!"\\mathit{He}_{#}", w!"T_{#}", w!"U_{#}"]
  constLean := [w!"Leanify.OrthogonalPolynomials.legendre", w!"Leanify.OrthogonalPolynomials.hermiteProb",
    w!"Leanify.OrthogonalPolynomials.chebT", w!"Leanify.OrthogonalPolynomials.chebU"]
  modules := [w!"Leanify.Library.OrthogonalPolynomialsModel"]
  notions := [
    polyC phrase!"Legendre polynomial of degree $v$" 0 "`P_n`, orthogonal on `[-1,1]`: Mathlib's `Polynomial.shiftedLegendre n` at `(1 - x)/2`",
    poly phrase!"Hermite polynomial of degree $v$" hermite "`H_n` (physicists'), orthogonal for `e^{-x²}`",
    poly phrase!"physicists' Hermite polynomial of degree $v$" hermite "`H_n`",
    polyC phrase!"probabilists' Hermite polynomial of degree $v$" 1 "`He_n`, orthogonal for `e^{-x²/2}` (Mathlib `Polynomial.hermite`)",
    poly phrase!"Laguerre polynomial of degree $v$" laguerre "`L_n`, orthogonal for `e^{-x}` on `[0,∞)`",
    polyC phrase!"Chebyshev polynomial of the first kind of degree $v$" 2 "`T_n`, `T_n(cos θ) = cos(nθ)` (Mathlib `Polynomial.Chebyshev.T`)",
    polyC phrase!"Chebyshev polynomial of the second kind of degree $v$" 3 "`U_n`, `U_n(cos θ) sin θ = sin((n+1)θ)` (Mathlib `Polynomial.Chebyshev.U`)"]

end Leanify.OrthogonalPolynomials
