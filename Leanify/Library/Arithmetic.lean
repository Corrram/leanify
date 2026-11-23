import Leanify.Library.Numbers

/-! # Vocabulary: arithmetic functions

The functions of elementary number theory, of positive integers: Euler's totient function,
the Möbius function, the number and the sums of powers of the divisors, the number of prime
factors, the prime-counting function, the `n`th prime, `p`-adic valuations, multiplicative
orders and sums of digits; perfect, abundant and deficient numbers; multiplicative
functions and the Dirichlet convolution.

A function is a notion of its own (`Let $\varphi$ denote Euler's totient function.`), and
so is its value (`the number of divisors of $n$`); an article fixes its notation itself
(`We write $\tau(n)$ for the number of divisors of $n$.`). The functions of Mathlib are
constants, interpreted by `Leanify/Library/ArithmeticModel.lean`; multiplicativity and the
Dirichlet convolution are terms of the core language. Primes, divisibility and the greatest
common divisor are in the field `numbers`. -/

namespace Leanify.Arithmetic
open Build Core

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def totient : Nat := 0
def moebius : Nat := 1
def numDivisors : Nat := 2
def sigma : Nat := 3
def primeCounting : Nat := 4
def nthPrime : Nat := 5
def omega : Nat := 6
def bigOmega : Nat := 7
def padicVal : Nat := 8
def orderMod : Nat := 9
def digitSum : Nat := 10
end Const
open Const

def posIntDom : Option Tm := some posInt
def natDom : Option Tm := some nonnegInt

/-- `a` and `n` have no common divisor but `±1`. -/
def coprime (a n : B) : B :=
  allInt fun d => imp (and (divides d a) (divides d n)) (or (eq d (num 1)) (eq d (neg (num 1))))

/-- A function of positive integers, as a real function defined on them. -/
def posFn (c : Nat) : Tm := close <| lamT .real (fun n => and (isInt n) (lt (num 0) n)) fun n => app (const c) n

/-- `σ(n)`, the sum of the divisors. -/
def sigma1 (n : B) : B := app2 (const sigma) (num 1) n

def perfect : Tm := predR fun n => and (and (isInt n) (lt (num 0) n)) (eq (sigma1 n) (mul (num 2) n))
def abundant : Tm := predR fun n => and (and (isInt n) (lt (num 0) n)) (lt (mul (num 2) n) (sigma1 n))
def deficient : Tm := predR fun n => and (and (isInt n) (lt (num 0) n)) (lt (sigma1 n) (mul (num 2) n))

/-- A prime of the form `2^k - 1`. -/
def mersenne : Tm := predR fun p =>
  and (Numbers.isPrime p) (exR fun k => and (isNat k) (eq p (sub (app2 (prim .rpow) (num 2) k) (num 1))))

/-- `f(1) = 1` and `f(mn) = f(m) f(n)` for coprime positive integers `m`, `n`. -/
def multiplicative : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f =>
  and (eq (app f (num 1)) (num 1)) (allR fun m => allR fun n =>
    imp (and (and (and (isInt m) (lt (num 0) m)) (and (isInt n) (lt (num 0) n))) (coprime m n))
      (eq (app f (mul m n)) (mul (app f m) (app f n))))

/-- `f(1) = 1` and `f(mn) = f(m) f(n)` for all positive integers `m`, `n`. -/
def completelyMultiplicative : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f =>
  and (eq (app f (num 1)) (num 1)) (allR fun m => allR fun n =>
    imp (and (and (isInt m) (lt (num 0) m)) (and (isInt n) (lt (num 0) n)))
      (eq (app f (mul m n)) (mul (app f m) (app f n))))

/-- `(f * g)(n) = ∑_{d ∣ n} f(d) g(n/d)` for positive integers `n`. -/
def dirichlet : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f => lamT Ty.rfun (fun _ => tt) fun g =>
  lamT .real (fun n => and (isInt n) (lt (num 0) n)) fun n =>
    app (app (app (prim .finSum) (num 1)) n) (lamR fun d =>
      cases (divides d n) (mul (app f d) (app g (div n d))) (num 0))

def fn1 (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, value := posFn c, ty := Ty.rfun, doc }

def of1 (name : Phrase) (value : Tm) (dom : Option Tm) (doc : String) : Notion :=
  { name, value, ty := .real ⟶ .real, doms := [dom], doc }

def of2 (name : Phrase) (value : Tm) (d1 d2 : Option Tm) (doc : String) : Notion :=
  { name, value, ty := .real ⟶ .real ⟶ .real, doms := [d1, d2], doc }

def sigmaOf : Tm := close <| lamR fun n => sigma1 n

/-- The multiplicative order of `a` modulo `n`, for `a` coprime to `n`. -/
def order : Tm := close <| lamT .real (fun a => isInt a) fun a =>
  lamT .real (fun n => and (isInt n) (lt (num 0) n)) fun n =>
    guard (coprime a n) (app2 (const orderMod) a n)

def digits10 : Tm := close <| lamR fun n => app2 (const digitSum) (num 10) n

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real,
    .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real]
  constNames := [w!"\\varphi", w!"\\mu", w!"\\tau", w!"\\sigma_{#1}(#2)", w!"\\pi", w!"\\operatorname{p}",
    w!"\\omega", w!"\\Omega", w!"\\nu_{#1}(#2)", w!"\\operatorname{ord}_{#2}(#1)", w!"\\operatorname{s}_{#1}(#2)"]
  constLean := [w!"Leanify.Arithmetic.totient", w!"Leanify.Arithmetic.moebius",
    w!"Leanify.Arithmetic.numDivisors", w!"Leanify.Arithmetic.sigma", w!"Leanify.Arithmetic.primeCounting",
    w!"Leanify.Arithmetic.nthPrime", w!"Leanify.Arithmetic.omega", w!"Leanify.Arithmetic.bigOmega",
    w!"Leanify.Arithmetic.padicVal", w!"Leanify.Arithmetic.orderMod", w!"Leanify.Arithmetic.digitSum"]
  modules := [w!"Leanify.Library.ArithmeticModel"]
  nouns := [
    noun phrase!"perfect number" phrase!"perfect numbers" perfect
      "a positive integer equal to the sum of its proper divisors: `σ(n) = 2n` (Mathlib `Nat.Perfect`)",
    noun phrase!"Mersenne prime" phrase!"Mersenne primes" mersenne "a prime `2^k - 1`",
    { sing := phrase!"arithmetic function", plural := phrase!"arithmetic functions", ty := Ty.rfun,
      pred := close (lamT Ty.rfun (fun _ => tt) fun _ => tt),
      doc := "a function of the positive integers, as a real function (Mathlib `ArithmeticFunction`)" }]
  mods := [
    adj phrase!"perfect" perfect "`σ(n) = 2n` (Mathlib `Nat.Perfect`)",
    adj phrase!"abundant" abundant "`σ(n) > 2n`",
    adj phrase!"deficient" deficient "`σ(n) < 2n`",
    { phrase := phrase!"multiplicative", prenominal := true, ty := Ty.rfun, pred := multiplicative,
      doc := "`f(1) = 1`, `f(mn) = f(m)f(n)` for coprime positive integers (Mathlib `ArithmeticFunction.IsMultiplicative`)" },
    { phrase := phrase!"completely multiplicative", prenominal := true, ty := Ty.rfun, pred := completelyMultiplicative,
      doc := "`f(1) = 1`, `f(mn) = f(m)f(n)` for all positive integers" }]
  notions := [
    fn1 phrase!"Euler's totient function" totient "`φ(n)`, the integers in `[1, n]` coprime to `n` (Mathlib `Nat.totient`)",
    fn1 phrase!"Möbius function" moebius "`μ(n)` (Mathlib `ArithmeticFunction.moebius`)",
    fn1 phrase!"Moebius function" moebius "`μ(n)` (Mathlib `ArithmeticFunction.moebius`)",
    fn1 phrase!"divisor counting function" numDivisors "`τ(n)`, the number of positive divisors (Mathlib `Nat.divisors`)",
    { name := phrase!"prime-counting function", value := .const primeCounting, ty := Ty.rfun,
      doc := "`π(x)`, the number of primes `≤ x` (Mathlib `Nat.primeCounting`)" },
    { name := phrase!"prime counting function", value := .const primeCounting, ty := Ty.rfun,
      doc := "`π(x)`, the number of primes `≤ x` (Mathlib `Nat.primeCounting`)" },
    of1 phrase!"number of divisors of $v$" (.const numDivisors) posIntDom
      "the number of positive divisors (Mathlib `(Nat.divisors n).card`)",
    of1 phrase!"number of positive divisors of $v$" (.const numDivisors) posIntDom
      "the number of positive divisors (Mathlib `(Nat.divisors n).card`)",
    of1 phrase!"sum of the divisors of $v$" sigmaOf posIntDom "`σ(n)` (Mathlib `ArithmeticFunction.sigma 1`)",
    of1 phrase!"sum of the positive divisors of $v$" sigmaOf posIntDom "`σ(n)` (Mathlib `ArithmeticFunction.sigma 1`)",
    of1 phrase!"sum of divisors of $v$" sigmaOf posIntDom "`σ(n)` (Mathlib `ArithmeticFunction.sigma 1`)",
    of2 phrase!"sum of the $v$th powers of the divisors of $v$" (.const sigma) natDom posIntDom
      "`σ_k(n)` (Mathlib `ArithmeticFunction.sigma k`)",
    of1 phrase!"number of primes not exceeding $v$" (.const primeCounting) none "`π(x)` (Mathlib `Nat.primeCounting`)",
    of1 phrase!"number of primes at most $v$" (.const primeCounting) none "`π(x)` (Mathlib `Nat.primeCounting`)",
    of1 phrase!"number of primes less than or equal to $v$" (.const primeCounting) none
      "`π(x)` (Mathlib `Nat.primeCounting`)",
    of1 phrase!"$v$th prime" (.const nthPrime) posIntDom "`p_1 = 2`, `p_2 = 3`, … (Mathlib `Nat.nth Nat.Prime (n - 1)`)",
    of1 phrase!"$v$th prime number" (.const nthPrime) posIntDom "`p_1 = 2`, `p_2 = 3`, … (Mathlib `Nat.nth Nat.Prime (n - 1)`)",
    of1 phrase!"number of distinct prime factors of $v$" (.const omega) posIntDom
      "`ω(n)` (Mathlib `ArithmeticFunction.cardDistinctFactors`)",
    of1 phrase!"number of distinct prime divisors of $v$" (.const omega) posIntDom
      "`ω(n)` (Mathlib `ArithmeticFunction.cardDistinctFactors`)",
    of1 phrase!"number of prime factors of $v$ counted with multiplicity" (.const bigOmega) posIntDom
      "`Ω(n)` (Mathlib `ArithmeticFunction.cardFactors`)",
    of2 phrase!"$v$-adic valuation of $v$" (.const padicVal) (some Numbers.prime) posIntDom
      "the exponent of the prime `p` in `n` (Mathlib `padicValNat`)",
    { name := phrase!"multiplicative order of $v$ modulo $v$", value := order, ty := .real ⟶ .real ⟶ .real,
      doc := "the least `k ≥ 1` with `a^k ≡ 1 (mod n)`, for `a` coprime to `n` (Mathlib `orderOf` in `ZMod n`)" },
    { name := phrase!"order of $v$ modulo $v$", value := order, ty := .real ⟶ .real ⟶ .real,
      doc := "the least `k ≥ 1` with `a^k ≡ 1 (mod n)`, for `a` coprime to `n` (Mathlib `orderOf` in `ZMod n`)" },
    of1 phrase!"sum of the digits of $v$" digits10 natDom "in base 10 (Mathlib `(Nat.digits 10 n).sum`)",
    of2 phrase!"sum of the digits of $v$ in base $v$" (close <| lamR fun n => lamR fun b => app2 (const digitSum) b n)
      natDom (some (predR fun b => and (isInt b) (le (num 2) b))) "(Mathlib `(Nat.digits b n).sum`)",
    { name := phrase!"Dirichlet convolution of $v$ and $v$", value := dirichlet, ty := Ty.rfun ⟶ Ty.rfun ⟶ Ty.rfun,
      doc := "`(f * g)(n) = ∑_{d ∣ n} f(d) g(n/d)` (Mathlib `ArithmeticFunction` multiplication)" }]

end Leanify.Arithmetic
