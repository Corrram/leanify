import Leanify.Library.Core

/-! # Vocabulary: rating systems

Paired-comparison models and rating updates (`We write $E(a,b)$ for the Elo expected score of a
player rated $a$ against a player rated $b$.`).

* notions: the Elo expected score `1/(1 + 10^{(R_b - R_a)/400})` and the update `R + K(S - E)`;
  the Bradley–Terry probability `a/(a+b)` that strength `a` beats strength `b`; the logistic win
  probability `1/(1 + e^{-d/s})` for a rating difference `d` and scale `s`; the Pythagorean
  expectation `S^x/(S^x + A^x)` for points scored `S` and allowed `A`.

Every meaning is a term of the core language. -/

namespace Leanify.Ratings
open Build Core

def pos (x : B) : B := lt (num 0) x
def rpow (x s : B) : B := app2 (prim .rpow) x s
def exp (x : B) : B := app (prim (.realFn .exp)) x

def vocab : Vocab where
  notions := [
    { name := phrase!"Elo expected score of a player rated $v$ against a player rated $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`1/(1 + 10^{(R_b - R_a)/400})`",
      value := close <| lamR fun a => lamR fun b => div (num 1) (add (num 1) (rpow (num 10) (div (sub b a) (num 400)))) },
    { name := phrase!"Elo update of the rating $v$ with factor $v$ for the score $v$ and the expected score $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ k => pos k, none, none], doc := "`R + K(S - E)`",
      value := close <| lamR fun r => lamT .real pos fun k => lamR fun s => lamR fun e => add r (mul k (sub s e)) },
    { name := phrase!"Bradley-Terry probability that the strength $v$ beats the strength $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ b => pos b], doc := "`a/(a+b)`",
      value := close <| lamT .real pos fun a => lamT .real pos fun b => div a (add a b) },
    { name := phrase!"logistic win probability for the rating difference $v$ with scale $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ s => pos s], doc := "`1/(1 + e^{-d/s})`",
      value := close <| lamR fun d => lamT .real pos fun s => div (num 1) (add (num 1) (exp (neg (div d s)))) },
    { name := phrase!"Pythagorean expectation for $v$ points scored and $v$ points allowed with exponent $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ a => pos a, dom3 .real fun _ _ x => pos x], doc := "`S^x/(S^x + A^x)`",
      value := close <| lamT .real pos fun s => lamT .real pos fun a => lamT .real pos fun x => div (rpow s x) (add (rpow s x) (rpow a x)) }]

end Leanify.Ratings
