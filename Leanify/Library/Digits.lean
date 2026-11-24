import Leanify.Library.Core

/-! # Vocabulary: digits

The base-`b` digits of a natural number (`b ≥ 2`): the `k`th digit counted from the right
and from `0`, the number of digits, the reversal, palindromes, the digital root, repunits,
Harshad and narcissistic numbers (`We write $d_k(n)$ for the $k$th digit of $n$ in base $10$.`).
The sum of the digits is in the field `arithmetic`.

* notions: the `k`th digit `⌊n/b^k⌋ - b⌊n/b^{k+1}⌋`, the number of digits of `n ≥ 1` (the `L`
  with `b^{L-1} ≤ n < b^L`), the digit reversal, the digital root of `n ≥ 1`
  (`n - 9⌊(n-1)/9⌋`), the `n`th repunit `(b^n - 1)/(b - 1)`;
* adjectives of numbers: `palindrome in base $b$`, `Harshad number` (divisible by the
  sum of its decimal digits), `narcissistic number` (the sum of the `L`th powers of its `L`
  decimal digits).

Every meaning is a term of the core language (floors, integer powers, finite sums). -/

namespace Leanify.Digits
open Build Core

def natP (k : B) : B := and (isInt k) (le (num 0) k)
def posInt (k : B) : B := and (isInt k) (le (num 1) k)
def base (b : B) : B := and (isInt b) (le (num 2) b)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def digit (b k n : B) : B := sub (floor (div n (zpow b k))) (mul b (floor (div n (zpow b (add k (num 1))))))
def len (b n : B) : B := theR fun l => and (posInt l) (and (le (zpow b (sub l (num 1))) n) (lt n (zpow b l)))
def rev (b n : B) : B := finSum (num 0) (sub (len b n) (num 1)) fun k => mul (digit b k n) (zpow b (sub (sub (len b n) (num 1)) k))
def digitSum10 (n : B) : B := finSum (num 0) n fun k => digit (num 10) k n

def harshad : Tm := predR fun n => and (posInt n) (isInt (div n (digitSum10 n)))
def narcissistic : Tm := predR fun n => and (posInt n) (eq (finSum (num 0) (sub (len (num 10) n) (num 1)) fun k =>
  zpow (digit (num 10) k n) (len (num 10) n)) n)

def vocab : Vocab where
  nouns := [
    noun phrase!"Harshad number" phrase!"Harshad numbers" harshad "a positive integer divisible by the sum of its decimal digits",
    noun phrase!"Niven number" phrase!"Niven numbers" harshad "a Harshad number",
    noun phrase!"narcissistic number" phrase!"narcissistic numbers" narcissistic "the sum of the `L`th powers of its `L` decimal digits",
    noun phrase!"Armstrong number" phrase!"Armstrong numbers" narcissistic "a narcissistic number"]
  mods := [
    { phrase := phrase!"palindrome in base $v$", prenominal := false, ty := .real,
      pred := close <| lamT .real base fun b => lamR fun n => and (posInt n) (eq (rev b n) n),
      doc := "a positive integer whose base-`b` digits read the same backwards" },
    { phrase := phrase!"Harshad number", prenominal := false, ty := .real,
      pred := harshad,
      doc := "a positive integer divisible by the sum of its decimal digits (a Niven number)" },
    { phrase := phrase!"narcissistic number", prenominal := false, ty := .real,
      pred := narcissistic,
      doc := "a positive integer equal to the sum of the `L`th powers of its `L` decimal digits (an Armstrong number)" }]
  notions := [
    { name := phrase!"$v$th digit of $v$ in base $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real natP, dom1 .real base],
      doc := "`⌊n/b^k⌋ - b⌊n/b^{k+1}⌋`, the digit of `b^k`, counted from `k = 0`",
      value := close <| lamT .real natP fun k => lamT .real natP fun n => lamT .real base fun b => digit b k n },
    { name := phrase!"number of digits of $v$ in base $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real base],
      doc := "the `L` with `b^{L-1} ≤ n < b^L`, for `n ≥ 1`",
      value := close <| lamT .real posInt fun n => lamT .real base fun b => len b n },
    { name := phrase!"digit reversal of $v$ in base $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real base],
      doc := "the number with the base-`b` digits of `n` in the reverse order",
      value := close <| lamT .real posInt fun n => lamT .real base fun b => rev b n },
    { name := phrase!"digital root of $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`n - 9⌊(n-1)/9⌋`: the repeated decimal digit sum, for `n ≥ 1`",
      value := close <| lamT .real posInt fun n => sub n (mul (num 9) (floor (div (sub n (num 1)) (num 9)))) },
    { name := phrase!"$v$th repunit in base $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real base],
      doc := "`(b^n - 1)/(b - 1)`, the number with `n` digits `1`",
      value := close <| lamT .real natP fun n => lamT .real base fun b => div (sub (zpow b n) (num 1)) (sub b (num 1)) }]

end Leanify.Digits
