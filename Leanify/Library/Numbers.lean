import Leanify.Library.Core

/-! # Vocabulary: numbers

Primes, divisibility, parity and the arithmetic of integers, as properties of real
numbers (Leanify's numbers are real numbers; `x ∈ ℤ` is `isInt x`). Every meaning is a
term of the core language, so the field has no constants and no model.

The words every article may use (*integer*, *real number*, *positive*, *rational
number*) are in the core vocabulary (`Leanify.Library.Core`), which is always there. -/

namespace Leanify.Numbers
open Build Core


/-- `p` is a prime number: an integer `p ≥ 2` whose only factorizations into
nonnegative integers are trivial. -/
def isPrime (p : B) : B :=
  and (isInt p) (and (le (num 2) p)
    (allR fun a => allR fun b =>
      imp (and (and (isNat a) (isNat b)) (eq (mul a b) p)) (or (eq a (num 1)) (eq b (num 1)))))

def prime : Tm := predR isPrime
def composite : Tm := predR fun x => and (and (isInt x) (le (num 2) x)) (not (isPrime x))
def even : Tm := predR fun x => exInt fun k => eq x (mul (num 2) k)
def odd : Tm := predR fun x => exInt fun k => eq x (add (mul (num 2) k) (num 1))
def perfectSquare : Tm := predR fun x => exInt fun k => eq x (mul k k)
/-- A product `p_1⋯p_k` of `k ≥ 1` primes (Mathlib `Nat.primeFactorsList`). -/
def productOfPrimes : Tm := predR fun n => exR fun k => and (and (isNat k) (le (num 1) k))
  (exT (.real ⟶ .real) fun p => and
    (allR fun i => imp (and (isInt i) (and (le (num 1) i) (le i k))) (isPrime (app p i)))
    (eq (app (app (app (prim .finProd) (num 1)) k) p) n))
/-- `a² + b² + c² + d²` for integers `a`, `b`, `c`, `d` (Mathlib `Nat.sum_four_squares`). -/
def sumOfFourSquares : Tm := predR fun n => exInt fun a => exInt fun b => exInt fun c => exInt fun d =>
  eq n (add (add (mul a a) (mul b b)) (add (mul c c) (mul d d)))
/-- `p + q` for primes `p`, `q`. -/
def sumOfTwoPrimes : Tm := predR fun n => exR fun p => exR fun q => and (and (isPrime p) (isPrime q)) (eq n (add p q))
/-- `a² - b²` for integers `a`, `b`. -/
def differenceOfTwoSquares : Tm := predR fun n => exInt fun a => exInt fun b => eq n (sub (mul a a) (mul b b))
def squarefree : Tm := predR fun x =>
  and (isInt x) (allInt fun k => imp (divides (mul k k) x) (eq (mul k k) (num 1)))

/-- The greatest common divisor of two integers, not both zero. -/
def gcd : Tm := close <| lamT .real (fun a => isInt a) fun a => lamT .real (fun b => isInt b) fun b =>
  theR fun d => and (and (isInt d) (lt (num 0) d)) (and (and (divides d a) (divides d b))
    (allInt fun e => imp (and (divides e a) (divides e b)) (le e d)))

/-- The least common multiple of two nonzero integers. -/
def lcm : Tm := close <| lamT .real (fun a => isInt a) fun a => lamT .real (fun b => isInt b) fun b =>
  theR fun m => and (and (isInt m) (lt (num 0) m)) (and (and (divides a m) (divides b m))
    (allInt fun e => imp (and (lt (num 0) e) (and (divides a e) (divides b e))) (le m e)))

/-- `a mod b` for an integer `a` and a positive integer `b`: `a - b ⌊a/b⌋`. -/
def remainder : Tm := close <| lamT .real (fun a => isInt a) fun a =>
  lamT .real (fun b => and (isInt b) (lt (num 0) b)) fun b => sub a (mul b (floor (div a b)))

/-- `⌊a/b⌋` for an integer `a` and a positive integer `b`. -/
def quotient : Tm := close <| lamT .real (fun a => isInt a) fun a =>
  lamT .real (fun b => and (isInt b) (lt (num 0) b)) fun b => floor (div a b)

def integerPart : Tm := close <| lamR fun x => floor x
def fractionalPart : Tm := close <| lamR fun x => sub x (floor x)
def absoluteValue : Tm := close <| lamR fun x => abs x

def intDom : Option Tm := some integer
def posIntDom : Option Tm := some posInt

def vocab : Vocab where
  nouns := [
    noun phrase!"prime number" phrase!"prime numbers" prime "a prime (Mathlib `Nat.Prime`)",
    noun phrase!"prime" phrase!"primes" prime "a prime (Mathlib `Nat.Prime`)",
    noun phrase!"composite number" phrase!"composite numbers" composite "an integer `≥ 2` that is not prime",
    noun phrase!"product of primes" phrase!"products of primes" productOfPrimes "`p_1⋯p_k` for primes `p_i`, `k ≥ 1` (Mathlib `Nat.primeFactorsList`)",
    noun phrase!"product of prime numbers" phrase!"products of prime numbers" productOfPrimes "`p_1⋯p_k` for primes `p_i`, `k ≥ 1`",
    noun phrase!"sum of four squares" phrase!"sums of four squares" sumOfFourSquares "`a² + b² + c² + d²` for integers",
    noun phrase!"sum of two primes" phrase!"sums of two primes" sumOfTwoPrimes "`p + q` for primes `p`, `q`",
    noun phrase!"difference of two squares" phrase!"differences of two squares" differenceOfTwoSquares "`a² - b²` for integers `a`, `b`",
    noun phrase!"perfect square" phrase!"perfect squares" perfectSquare "`x = k²` for an integer `k` (Mathlib `IsSquare` in `ℤ`)",
    { noun phrase!"divisor" phrase!"divisors" (close <| lamR fun d => isInt d) "an integer `d` with `d ∣ n` (Mathlib `Int.instDvd`)" with
      arg := some ([w!"of"], .real, close <| lamR fun n => lamR fun d => and (isInt n) (divides d n)) },
    { noun phrase!"positive divisor" phrase!"positive divisors" (close <| lamR fun d => and (isInt d) (lt (num 0) d))
        "a divisor `d ≥ 1` (Mathlib `Nat.divisors`)" with
      arg := some ([w!"of"], .real, close <| lamR fun n => lamR fun d => and (isInt n) (divides d n)) },
    { noun phrase!"prime divisor" phrase!"prime divisors" prime "a prime `p` with `p ∣ n` (Mathlib `Nat.primeFactors`)" with
      arg := some ([w!"of"], .real, close <| lamR fun n => lamR fun d => and (isInt n) (divides d n)) },
    { noun phrase!"prime factor" phrase!"prime factors" prime "a prime `p` with `p ∣ n` (Mathlib `Nat.primeFactors`)" with
      arg := some ([w!"of"], .real, close <| lamR fun n => lamR fun d => and (isInt n) (divides d n)) }]
  mods := [
    adj phrase!"even" even "`x = 2k` for an integer `k` (Mathlib `Even`)",
    adj phrase!"odd" odd "`x = 2k+1` for an integer `k` (Mathlib `Odd`)",
    adj phrase!"prime" prime "prime (Mathlib `Nat.Prime`)",
    adj phrase!"composite" composite "an integer `≥ 2` that is not prime",
    adj phrase!"squarefree" squarefree "an integer not divisible by the square of an integer other than ±1 (Mathlib `Squarefree`)"]
  notions := [
    { name := phrase!"greatest common divisor of $v$ and $v$", value := gcd, ty := .real ⟶ .real ⟶ .real,
      doms := [intDom, intDom], doc := "the largest positive common divisor; defined unless both are 0 (Mathlib `Int.gcd`)" },
    { name := phrase!"least common multiple of $v$ and $v$", value := lcm, ty := .real ⟶ .real ⟶ .real,
      doms := [intDom, intDom], doc := "the smallest positive common multiple; defined when both are nonzero (Mathlib `Int.lcm`)" },
    { name := phrase!"remainder of $v$ modulo $v$", value := remainder, ty := .real ⟶ .real ⟶ .real,
      doms := [intDom, posIntDom], doc := "`a - b⌊a/b⌋` for `b > 0` (Mathlib `Int.emod`)" },
    { name := phrase!"quotient of $v$ by $v$", value := quotient, ty := .real ⟶ .real ⟶ .real,
      doms := [intDom, posIntDom], doc := "`⌊a/b⌋` for `b > 0` (Mathlib `Int.ediv`)" },
    { name := phrase!"integer part of $v$", value := integerPart, ty := .real ⟶ .real,
      doc := "`⌊x⌋` (Mathlib `Int.floor`)" },
    { name := phrase!"fractional part of $v$", value := fractionalPart, ty := .real ⟶ .real,
      doc := "`x - ⌊x⌋` (Mathlib `Int.fract`)" },
    { name := phrase!"absolute value of $v$", value := absoluteValue, ty := .real ⟶ .real,
      doc := "`|x|`" }]

end Leanify.Numbers
