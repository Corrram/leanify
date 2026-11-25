import Leanify.Library.Core

/-! # Vocabulary: words and necklaces

Counts of words over a finite alphabet (`We write $W(n,k)$ for the number of words of length $n$
over $k$ letters.`). Subsets, maps and compositions are in the field `counting`.

* notions: the numbers of words `k^n`, of palindromes `k^{⌈n/2⌉}` and of words with no two equal
  adjacent letters `k(k-1)^{n-1}` of length `n` over `k` letters; the number of binary words of
  length `n` without two consecutive ones (`F_{n+2}`, as `∑_j \binom{n+1-j}{j}`); the number
  `(1/n)∑_{i=1}^{n} k^{gcd(i,n)}` of necklaces (Burnside); the number `(k!)^{k^{n-1}}/k^n` of de
  Bruijn sequences of order `n` (BEST theorem).

Every meaning is a term of the core language. -/

namespace Leanify.Words
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def ceil (x : B) : B := app (prim .ceil) x
def binom (n k : B) : B := app2 (prim .binom) n k
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def common (d a b : B) : B := and (divides d a) (divides d b)
def gcd (a b : B) : B := theR fun d => and (posInt d) (and (common d a b) (allR fun e => imp (and (posInt e) (common e a b)) (le e d)))
def two (name : Phrase) (d1 d2 : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ k => d2 k], doc,
    value := close <| lamT .real d1 fun n => lamT .real d2 fun k => body n k }

def vocab : Vocab where
  notions := [
    two phrase!"number of words of length $v$ over $v$ letters" natP posInt (fun n k => zpow k n) "`k^n`",
    two phrase!"number of palindromes of length $v$ over $v$ letters" natP posInt (fun n k => zpow k (ceil (div n (num 2)))) "`k^{⌈n/2⌉}`",
    two phrase!"number of words of length $v$ over $v$ letters with no two equal adjacent letters" posInt posInt
      (fun n k => mul k (zpow (sub k (num 1)) (sub n (num 1)))) "`k(k-1)^{n-1}`",
    { name := phrase!"number of binary words of length $v$ without two consecutive ones", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "`F_{n+2} = ∑_{j=0}^{n} \\binom{n+1-j}{j}`",
      value := close <| lamT .real natP fun n => finSum (num 0) n fun j => binom (sub (add n (num 1)) j) j },
    two phrase!"number of necklaces of length $v$ over $v$ colours" posInt posInt
      (fun n k => div (finSum (num 1) n fun i => zpow k (gcd i n)) n) "`(1/n)∑_{i=1}^{n} k^{gcd(i,n)}`: words up to rotation",
    two phrase!"number of de Bruijn sequences of order $v$ over $v$ letters" posInt posInt
      (fun n k => div (zpow (fact k) (zpow k (sub n (num 1)))) (zpow k n)) "`(k!)^{k^{n-1}}/k^n`, as cyclic sequences"]

end Leanify.Words
