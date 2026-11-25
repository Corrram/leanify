import Leanify.Library.Core

/-! # Vocabulary: voting and apportionment

Quotas and divisors of electoral systems, and counts of social choice (`We write $q(V,S)$ for
the Droop quota for $V$ votes and $S$ seats.`).

* notions: the Hare quota `V/S`, the Droop quota `⌊V/(S+1)⌋ + 1` and the majority quota
  `⌊V/2⌋ + 1`; the D'Hondt quotient `V/(s+1)` and the Webster (Sainte-Laguë) quotient
  `V/(2s+1)` of a party with `V` votes after `s` seats; the number `n(n-1)/2` of pairwise
  contests among `n` candidates; the largest Borda score `(n-1)m` with `n` candidates and `m`
  voters.

Every meaning is a term of the core language. -/

namespace Leanify.Voting
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def two (name : Phrase) (d1 d2 : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ y => d2 y], doc,
    value := close <| lamT .real d1 fun x => lamT .real d2 fun y => body x y }
def one (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real d], doc, value := close <| lamT .real d body }

def vocab : Vocab where
  notions := [
    two phrase!"Hare quota for $v$ votes and $v$ seats" natP posInt (fun v s => div v s) "`V/S`",
    two phrase!"Droop quota for $v$ votes and $v$ seats" natP posInt (fun v s => add (floor (div v (add s (num 1)))) (num 1))
      "`⌊V/(S+1)⌋ + 1`",
    one phrase!"majority quota for $v$ votes" natP (fun v => add (floor (div v (num 2))) (num 1)) "`⌊V/2⌋ + 1`",
    two phrase!"D'Hondt quotient of $v$ votes after $v$ seats" natP natP (fun v s => div v (add s (num 1))) "`V/(s+1)`",
    two phrase!"Webster quotient of $v$ votes after $v$ seats" natP natP (fun v s => div v (add (mul (num 2) s) (num 1)))
      "`V/(2s+1)` (Sainte-Laguë)",
    one phrase!"number of pairwise contests among $v$ candidates" natP (fun n => div (mul n (sub n (num 1))) (num 2)) "`n(n-1)/2`",
    two phrase!"largest Borda score with $v$ candidates and $v$ voters" posInt natP (fun n m => mul (sub n (num 1)) m)
      "`(n-1)m`: first place on every ballot"]

end Leanify.Voting
