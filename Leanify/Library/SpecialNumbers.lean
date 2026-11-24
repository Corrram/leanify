import Leanify.Library.Numbers

/-! # Vocabulary: special kinds of integers

Kinds of integers and named integer sequences of elementary number theory, as properties of
real numbers (Leanify's integers are real numbers with `isInt`).

* adjectives of integers: `perfect cube`, `perfect power` (`m^k`, `k ≥ 2`), `sum of two
  squares`, `triangular`, `twin prime`, `Sophie Germain prime` (`2p + 1` prime), `safe
  prime` (`(p - 1)/2` prime), `Fermat prime`, `power of two`, `power of $b$`;
* notions: the `n`th Fermat number `2^{2^n} + 1`, the `n`th Mersenne number `2^n - 1`, the
  `n`th repunit `(10^n - 1)/9`, the `n`th square, pentagonal, tetrahedral and square
  pyramidal numbers, the `n`th oblong number `n(n+1)`.

Every meaning is a term of the core language, with the primes of the field `numbers`. -/

namespace Leanify.SpecialNumbers
open Build Core

def zpow (x k : B) : B := app2 (prim .zpow) x k
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posIntP (n : B) : B := and (isInt n) (lt (num 0) n)
def prime (p : B) : B := Numbers.isPrime p
def exInt (body : B → B) : B := exR fun k => and (isInt k) (body k)
def exNat (body : B → B) : B := exR fun k => and (natP k) (body k)

def adjN (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := .real, pred := predR body, doc }
def nth (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real natP], doc, value := close <| lamT .real natP body }

def vocab : Vocab where
  nouns := [
    noun phrase!"perfect cube" phrase!"perfect cubes" (predR fun x => and (isInt x) (exInt fun m => eq x (mul (mul m m) m)))
      "`m³` for an integer `m`",
    noun phrase!"perfect power" phrase!"perfect powers"
      (predR fun x => and (isInt x) (exInt fun m => exNat fun k => and (le (num 2) k) (eq x (zpow m k))))
      "`m^k` for integers `m` and `k ≥ 2`",
    noun phrase!"twin prime" phrase!"twin primes" (predR fun p => and (prime p) (or (prime (add p (num 2))) (prime (sub p (num 2)))))
      "a prime `p` with `p - 2` or `p + 2` prime",
    noun phrase!"Sophie Germain prime" phrase!"Sophie Germain primes"
      (predR fun p => and (prime p) (prime (add (mul (num 2) p) (num 1)))) "a prime `p` with `2p + 1` prime",
    noun phrase!"safe prime" phrase!"safe primes" (predR fun p => and (prime p) (prime (div (sub p (num 1)) (num 2))))
      "a prime `p` with `(p - 1)/2` prime",
    noun phrase!"Fermat prime" phrase!"Fermat primes"
      (predR fun p => and (prime p) (exNat fun n => eq p (add (zpow (num 2) (zpow (num 2) n)) (num 1))))
      "a prime of the form `2^{2^n} + 1`",
    noun phrase!"power of two" phrase!"powers of two" (predR fun x => exNat fun k => eq x (zpow (num 2) k)) "`2^k`, `k ≥ 0`"]
  mods := [
    adjN phrase!"sum of two squares" false (fun x => and (isInt x) (exInt fun a => exInt fun b => eq x (add (mul a a) (mul b b))))
      "`a² + b²` for integers `a`, `b`",
    adjN phrase!"triangular" true (fun x => exNat fun k => eq x (div (mul k (add k (num 1))) (num 2))) "`k(k+1)/2` for some `k ≥ 0`",
    { phrase := phrase!"power of $v$", prenominal := false, ty := .real,
      pred := close <| lamR fun b => lamR fun x => exNat fun k => eq x (zpow b k), doc := "`b^k`, `k ≥ 0`" }]
  notions := [
    nth phrase!"$v$th Fermat number" (fun n => add (zpow (num 2) (zpow (num 2) n)) (num 1)) "`2^{2^n} + 1`",
    nth phrase!"$v$th Mersenne number" (fun n => sub (zpow (num 2) n) (num 1)) "`2^n - 1`",
    nth phrase!"$v$th repunit" (fun n => div (sub (zpow (num 10) n) (num 1)) (num 9)) "`(10^n - 1)/9`: `n` digits `1`",
    nth phrase!"$v$th square number" (fun n => mul n n) "`n²`",
    nth phrase!"$v$th pentagonal number" (fun n => div (mul n (sub (mul (num 3) n) (num 1))) (num 2)) "`n(3n-1)/2`",
    nth phrase!"$v$th tetrahedral number" (fun n => div (mul (mul n (add n (num 1))) (add n (num 2))) (num 6)) "`n(n+1)(n+2)/6`",
    nth phrase!"$v$th square pyramidal number" (fun n => div (mul (mul n (add n (num 1))) (add (mul (num 2) n) (num 1))) (num 6))
      "`n(n+1)(2n+1)/6`",
    nth phrase!"$v$th oblong number" (fun n => mul n (add n (num 1))) "`n(n+1)`"]

end Leanify.SpecialNumbers
