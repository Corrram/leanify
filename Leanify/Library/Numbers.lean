import Leanify.Library.Build

/-! # Vocabulary: numbers

Integers, primes, divisibility and rational numbers, as properties of real numbers
(Leanify's numbers are real numbers; `x ∈ ℤ` is `isInt x`). Every meaning is a
term of the core language, so the field has no constants and no model.

*Natural number* has two meanings in this field (with and without 0), so Leanify
does not read it alone: an article says *nonnegative integer* or *positive
integer*, or states its convention (`By a natural number we mean a nonnegative
integer.`). -/

namespace Leanify.Numbers
open Build

def integer : Tm := predR isInt
def nonnegInt : Tm := predR fun x => and (isInt x) (le (num 0) x)
def posInt : Tm := predR fun x => and (isInt x) (lt (num 0) x)
def negInt : Tm := predR fun x => and (isInt x) (lt x (num 0))

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
def rational : Tm := predR fun x => exInt fun p => exInt fun q => and (ne q (num 0)) (eq x (div p q))
def irrational : Tm := predR fun x => not (exInt fun p => exInt fun q => and (ne q (num 0)) (eq x (div p q)))
def nonzero : Tm := predR fun x => ne x (num 0)
def perfectSquare : Tm := predR fun x => exInt fun k => eq x (mul k k)
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

/-- A noun with the usual plural (`s`). -/
def noun (sing plural : Phrase) (pred : Tm) (doc : String) : Noun :=
  { sing, plural, ty := .real, pred, doc }

def adj (p : Phrase) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := true, ty := .real, pred, doc }

def vocab : Vocab where
  nouns := [
    noun phrase!"integer" phrase!"integers" integer "an integer: `x ∈ ℤ` (Mathlib `Int`, as a real number)",
    noun phrase!"real number" phrase!"real numbers" (predR fun _ => tt) "a real number (`ℝ`)",
    noun phrase!"real" phrase!"reals" (predR fun _ => tt) "a real number (`ℝ`), as in `for every real $x$`",
    noun phrase!"nonnegative integer" phrase!"nonnegative integers" nonnegInt "`x ∈ ℤ`, `0 ≤ x` (Mathlib `ℕ`)",
    noun phrase!"positive integer" phrase!"positive integers" posInt "`x ∈ ℤ`, `0 < x` (Mathlib `ℕ+`)",
    noun phrase!"negative integer" phrase!"negative integers" negInt "`x ∈ ℤ`, `x < 0`",
    { noun phrase!"natural number" phrase!"natural numbers" nonnegInt "with 0, as in Mathlib (`ℕ`)" with
      field := w!"with 0" },
    { noun phrase!"natural number" phrase!"natural numbers" posInt "without 0 (`ℕ+`)" with
      field := w!"without 0" },
    noun phrase!"prime number" phrase!"prime numbers" prime "a prime (Mathlib `Nat.Prime`)",
    noun phrase!"prime" phrase!"primes" prime "a prime (Mathlib `Nat.Prime`)",
    noun phrase!"composite number" phrase!"composite numbers" composite "an integer `≥ 2` that is not prime",
    noun phrase!"rational number" phrase!"rational numbers" rational "`x ∈ ℚ` (Mathlib `Set.range ((↑) : ℚ → ℝ)`)",
    noun phrase!"irrational number" phrase!"irrational numbers" irrational "`x ∉ ℚ` (Mathlib `Irrational`)",
    noun phrase!"perfect square" phrase!"perfect squares" perfectSquare "`x = k²` for an integer `k` (Mathlib `IsSquare` in `ℤ`)"]
  mods := [
    adj phrase!"even" even "`x = 2k` for an integer `k` (Mathlib `Even`)",
    adj phrase!"odd" odd "`x = 2k+1` for an integer `k` (Mathlib `Odd`)",
    adj phrase!"prime" prime "prime (Mathlib `Nat.Prime`)",
    adj phrase!"composite" composite "an integer `≥ 2` that is not prime",
    adj phrase!"rational" rational "`x ∈ ℚ`",
    adj phrase!"irrational" irrational "`x ∉ ℚ` (Mathlib `Irrational`)",
    adj phrase!"nonzero" nonzero "`x ≠ 0`",
    adj phrase!"positive" (predR fun x => lt (num 0) x) "`x > 0`",
    adj phrase!"negative" (predR fun x => lt x (num 0)) "`x < 0`",
    adj phrase!"nonnegative" (predR fun x => le (num 0) x) "`x ≥ 0`",
    adj phrase!"nonpositive" (predR fun x => le x (num 0)) "`x ≤ 0`",
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
