import Leanify.Library.Core

/-! # Vocabulary: words and necklaces

Counts of words over a finite alphabet (`We write $W(n,k)$ for the number of words of length $n$
over $k$ letters.`). Subsets, maps and compositions are in the field `counting`.

* notions: the numbers of words, of palindromes and of words with no two equal adjacent letters
  of length `n` over `k` letters; the number of binary words of length `n` without two
  consecutive ones; the number of necklaces of length `n` over `k` colours (words up to
  rotation); the number of de Bruijn sequences of order `n` over `k` letters (as cyclic
  sequences).

The counts are constants, interpreted by the declarations of `Leanify/Library/WordsModel.lean`:
the number of elements of the type of the words counted (`Fin n → Fin k` with the property; the
classes of the cyclic words `ZMod n → Fin k` under rotation). Their closed forms (`k^{⌈n/2⌉}`,
`F_{n+2}`, Burnside's `(1/n)∑_{i=1}^{n} k^{gcd(i,n)}`, the BEST theorem's
`(k!)^{k^{n-1}}/k^n`) are theorems, not definitions. -/

namespace Leanify.Words
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def words : Nat := 0
def palindromes : Nat := 1
def noEqualAdjacent : Nat := 2
def noConsecutiveOnes : Nat := 3
def necklaces : Nat := 4
def deBruijn : Nat := 5
end Const

/-- A count of the length and the number of letters, the constant `c`. -/
def two (name : Phrase) (d1 d2 : B → B) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ k => d2 k], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real]
  constNames := [w!"\\operatorname{Words}(#1,#2)", w!"\\operatorname{Pal}(#1,#2)", w!"\\operatorname{Words}^{\\neq}(#1,#2)",
    w!"\\operatorname{Fib}^{*}", w!"\\operatorname{Neck}(#1,#2)", w!"\\operatorname{dB}(#1,#2)"]
  constLean := [w!"Leanify.Words.words", w!"Leanify.Words.palindromes", w!"Leanify.Words.noEqualAdjacent",
    w!"Leanify.Words.noConsecutiveOnes", w!"Leanify.Words.necklaces", w!"Leanify.Words.deBruijn"]
  modules := [w!"Leanify.Library.WordsModel"]
  notions := [
    two phrase!"number of words of length $v$ over $v$ letters" natP posInt Const.words
      "the words `Fin n → Fin k` (`k^n`)",
    two phrase!"number of palindromes of length $v$ over $v$ letters" natP posInt Const.palindromes
      "the words of length `n` that read the same backwards (`k^{⌈n/2⌉}`)",
    two phrase!"number of words of length $v$ over $v$ letters with no two equal adjacent letters" posInt posInt
      Const.noEqualAdjacent "the words of length `n` whose adjacent letters differ (`k(k-1)^{n-1}`)",
    { name := phrase!"number of binary words of length $v$ without two consecutive ones", ty := .real ⟶ .real,
      doms := [dom1 .real natP], value := .const Const.noConsecutiveOnes,
      doc := "the words `Fin n → Bool` without two adjacent `true` (`F_{n+2}`)" },
    two phrase!"number of necklaces of length $v$ over $v$ colours" posInt posInt Const.necklaces
      "the classes of the cyclic words `ZMod n → Fin k` under rotation (`(1/n)∑_{i=1}^{n} k^{gcd(i,n)}`, Burnside)",
    two phrase!"number of de Bruijn sequences of order $v$ over $v$ letters" posInt posInt Const.deBruijn
      "the cyclic words of length `k^n` in which every word of length `n` occurs exactly once, up to rotation (`(k!)^{k^{n-1}}/k^n`, BEST)"]

end Leanify.Words
