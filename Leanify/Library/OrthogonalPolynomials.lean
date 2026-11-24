import Leanify.Library.Core

/-! # Vocabulary: classical orthogonal polynomials

The Legendre, Hermite, Laguerre and Chebyshev polynomials of degree `n`, each a real
function given by its explicit sum (`We write $P_n$ for the Legendre polynomial of degree
$n$.`, then `P_n(x)`), and the Gamma-free generalized binomial coefficient they use.

* `Legendre polynomial of degree $n$`: `∑_{k=0}^{n} \binom{n}{k}² ((x-1)/2)^{n-k} ((x+1)/2)^k`;
* `Hermite polynomial of degree $n$` (the physicists'): `n! ∑_{m=0}^{⌊n/2⌋} (-1)^m (2x)^{n-2m}/(m!(n-2m)!)`;
* `probabilists' Hermite polynomial of degree $n$`: `n! ∑_{m} (-1)^m x^{n-2m}/(2^m m!(n-2m)!)`;
* `Laguerre polynomial of degree $n$`: `∑_{k=0}^{n} \binom{n}{k} (-x)^k/k!`;
* `Chebyshev polynomial of the first kind of degree $n$`:
  `∑_{k=0}^{⌊n/2⌋} \binom{n}{2k} (x²-1)^k x^{n-2k}`;
* `Chebyshev polynomial of the second kind of degree $n$`:
  `∑_{k=0}^{⌊n/2⌋} \binom{n+1}{2k+1} (x²-1)^k x^{n-2k}`.

Every meaning is a term of the core language (finite sums, binomial coefficients,
factorials and integer powers), for a degree `n ≥ 0`; Mathlib's counterparts are
`Polynomial.legendre`-style definitions by recurrence (`Polynomial.hermite`,
`Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.U`). -/

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

def legendre (n x : B) : B :=
  finSum (num 0) n fun k => mul (mul (binom n k) (binom n k))
    (mul (zpow (div (sub x (num 1)) (num 2)) (sub n k)) (zpow (div (add x (num 1)) (num 2)) k))
def hermite (n x : B) : B :=
  mul (fact n) (finSum (num 0) (half n) fun m =>
    div (mul (sign m) (zpow (mul (num 2) x) (sub n (mul (num 2) m)))) (mul (fact m) (fact (sub n (mul (num 2) m)))))
def hermiteProb (n x : B) : B :=
  mul (fact n) (finSum (num 0) (half n) fun m =>
    div (mul (sign m) (zpow x (sub n (mul (num 2) m)))) (mul (mul (zpow (num 2) m) (fact m)) (fact (sub n (mul (num 2) m)))))
def laguerre (n x : B) : B := finSum (num 0) n fun k => div (mul (binom n k) (zpow (neg x) k)) (fact k)
def chebT (n x : B) : B :=
  finSum (num 0) (half n) fun k => mul (binom n (mul (num 2) k)) (mul (zpow (sub (mul x x) (num 1)) k) (zpow x (sub n (mul (num 2) k))))
def chebU (n x : B) : B :=
  finSum (num 0) (half n) fun k =>
    mul (binom (add n (num 1)) (add (mul (num 2) k) (num 1))) (mul (zpow (sub (mul x x) (num 1)) k) (zpow x (sub n (mul (num 2) k))))

def poly (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F, doms := [dom1 .real natP], doc, value := close <| lamT .real natP fun n => lamR fun x => body n x }

def vocab : Vocab where
  notions := [
    poly phrase!"Legendre polynomial of degree $v$" legendre "`P_n`, orthogonal on `[-1,1]` (Mathlib `Polynomial.shiftedLegendre`, shifted)",
    poly phrase!"Hermite polynomial of degree $v$" hermite "`H_n` (physicists'), orthogonal for `e^{-x²}`",
    poly phrase!"physicists' Hermite polynomial of degree $v$" hermite "`H_n`",
    poly phrase!"probabilists' Hermite polynomial of degree $v$" hermiteProb "`He_n`, orthogonal for `e^{-x²/2}` (Mathlib `Polynomial.hermite`)",
    poly phrase!"Laguerre polynomial of degree $v$" laguerre "`L_n`, orthogonal for `e^{-x}` on `[0,∞)`",
    poly phrase!"Chebyshev polynomial of the first kind of degree $v$" chebT "`T_n`, `T_n(cos θ) = cos(nθ)` (Mathlib `Polynomial.Chebyshev.T`)",
    poly phrase!"Chebyshev polynomial of the second kind of degree $v$" chebU "`U_n`, `U_n(cos θ) sin θ = sin((n+1)θ)` (Mathlib `Polynomial.Chebyshev.U`)"]

end Leanify.OrthogonalPolynomials
