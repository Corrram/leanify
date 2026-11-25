import Leanify.Library.Numbers

/-! # Vocabulary: analytic number theory

The functions of the distribution of primes (`We write $\vartheta(x)$ for the first Chebyshev
function at $x$.`): Chebyshev's functions, the von Mangoldt function, the logarithmic integral
and the counting functions of twin primes and of primes in a residue class. The prime-counting
function is in the field `arithmetic`.

* notions: the von Mangoldt function `Λ(n)` (`log p` if `n` is a power `p^k`, `k ≥ 1`, of a prime
  `p`, `0` otherwise), the first and second Chebyshev functions `ϑ(x) = ∑_{p ≤ x} log p` and
  `ψ(x) = ∑_{n ≤ x} Λ(n)`, the offset logarithmic integral `Li(x) = ∫_2^x dt/log t` (`x ≥ 2`), the
  number of primes up to `x` congruent to `a` modulo `q`, the number of twin prime pairs
  `(p, p+2)` with `p ≤ x`, the prime gap `p_{n+1} - p_n` (the `n`th prime is in `arithmetic`), and the sum of
  the reciprocals of the primes up to `x`.

Every meaning is a term of the core language with the primality of the field `numbers`. -/

namespace Leanify.AnalyticNumberTheory
open Build Core

def log (x : B) : B := app (prim (.realFn .log)) x
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def prime (p : B) : B := Numbers.isPrime p
def ind (c : B) : B := cases c (num 1) (num 0)
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def isPrimePower (n p : B) : B := and (prime p) (exR fun k => and (and (isInt k) (le (num 1) k)) (eq (zpow p k) n))
def mangoldt (n : B) : B := cases (exR fun p => isPrimePower n p) (log (theR fun p => isPrimePower n p)) (num 0)
def upTo (x : B) (body : B → B) : B := finSum (num 2) (floor x) body
def countPrimes (x : B) (cond : B → B) : B := upTo x fun p => ind (and (prime p) (cond p))
def nthPrime (n : B) : B := theR fun p => and (prime p) (eq (countPrimes p fun _ => tt) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def tt' (_ : B) : B := tt

def vocab : Vocab where
  notions := [
    { name := phrase!"von Mangoldt function at $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`Λ(n) = log p` if `n = p^k`, `k ≥ 1`, `0` otherwise (Mathlib `ArithmeticFunction.vonMangoldt`)",
      value := close <| lamT .real posInt mangoldt },
    { name := phrase!"first Chebyshev function at $v$", ty := .real ⟶ .real,
      doc := "`ϑ(x) = ∑_{p ≤ x} log p`", value := close <| lamR fun x => upTo x fun p => mul (ind (prime p)) (log p) },
    { name := phrase!"second Chebyshev function at $v$", ty := .real ⟶ .real,
      doc := "`ψ(x) = ∑_{n ≤ x} Λ(n)`", value := close <| lamR fun x => upTo x mangoldt },
    { name := phrase!"offset logarithmic integral at $v$", ty := .real ⟶ .real, doms := [dom1 .real fun x => le (num 2) x],
      doc := "`Li(x) = ∫_2^x dt/log t`, `x ≥ 2`",
      value := close <| lamT .real (fun x => le (num 2) x) fun x => integral (num 2) x (lamR fun t => div (num 1) (log t)) },
    { name := phrase!"number of primes up to $v$ congruent to $v$ modulo $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real isInt, dom1 .real posInt],
      doc := "`#{p ≤ x prime : p ≡ a (mod q)}`",
      value := close <| lamR fun x => lamT .real isInt fun a => lamT .real posInt fun q =>
        countPrimes x fun p => isInt (div (sub p a) q) },
    { name := phrase!"number of twin prime pairs up to $v$", ty := .real ⟶ .real,
      doc := "`#{p ≤ x : p and p + 2 prime}`", value := close <| lamR fun x => countPrimes x fun p => prime (add p (num 2)) },
    { name := phrase!"$v$th prime gap", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`p_{n+1} - p_n`", value := close <| lamT .real posInt fun n => sub (nthPrime (add n (num 1))) (nthPrime n) },
    { name := phrase!"sum of the reciprocals of the primes up to $v$", ty := .real ⟶ .real,
      doc := "`∑_{p ≤ x} 1/p`", value := close <| lamR fun x => upTo x fun p => mul (ind (prime p)) (div (num 1) p) }]

end Leanify.AnalyticNumberTheory
