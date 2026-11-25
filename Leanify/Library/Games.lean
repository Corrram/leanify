import Leanify.Library.Core

/-! # Vocabulary: two-person zero-sum games

Games of two players with two strategies each, given by the row player's payoffs `a`,
`b` (first row) and `c`, `d` (second row): `the value of the zero-sum game with payoffs $a$,
$b$, $c$ and $d$`. The row player plays the first strategy with probability `p`.

* notions: the value (`max_p min(pa + (1-p)c, pb + (1-p)d)`, von Neumann's minimax value), the
  lower value `max(min(a,b), min(c,d))` and the upper value `min(max(a,c), max(b,d))` in pure
  strategies, the expected payoff of mixed strategies `p`, `q`;
* adjectives: `optimal strategy for the row player in the zero-sum game with payoffs $a$,
  $b$, $c$ and $d$` (a `p ∈ [0,1]` that guarantees the value), `… for the column player …`.

Every meaning is a term of the core language. -/

namespace Leanify.Games
open Build Core

def prob (p : B) : B := and (le (num 0) p) (le p (num 1))
def mn (x y : B) : B := app2 (prim .min) x y
def mx (x y : B) : B := app2 (prim .max) x y
def guarantee (a b c d p : B) : B := mn (add (mul p a) (mul (sub (num 1) p) c)) (add (mul p b) (mul (sub (num 1) p) d))
def colLoss (a b c d q : B) : B := mx (add (mul q a) (mul (sub (num 1) q) b)) (add (mul q c) (mul (sub (num 1) q) d))
def value (a b c d : B) : B :=
  theR fun v => and (exR fun p => and (prob p) (eq (guarantee a b c d p) v)) (allR fun p => imp (prob p) (le (guarantee a b c d p) v))
def game (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real, doc,
    value := close <| lamR fun a => lamR fun b => lamR fun c => lamR fun d => body a b c d }

def vocab : Vocab where
  mods := [
    { phrase := phrase!"optimal strategy for the row player in the zero-sum game with payoffs $v$, $v$, $v$ and $v$",
      prenominal := false, ty := .real,
      pred := close <| lamR fun a => lamR fun b => lamR fun c => lamR fun d => lamR fun p =>
        and (prob p) (eq (guarantee a b c d p) (value a b c d)),
      doc := "`p ∈ [0,1]` with `min(pa + (1-p)c, pb + (1-p)d)` the value" },
    { phrase := phrase!"optimal strategy for the column player in the zero-sum game with payoffs $v$, $v$, $v$ and $v$",
      prenominal := false, ty := .real,
      pred := close <| lamR fun a => lamR fun b => lamR fun c => lamR fun d => lamR fun q =>
        and (prob q) (eq (colLoss a b c d q) (value a b c d)),
      doc := "`q ∈ [0,1]` with `max(qa + (1-q)b, qc + (1-q)d)` the value" }]
  notions := [
    game phrase!"value of the zero-sum game with payoffs $v$, $v$, $v$ and $v$" value
      "`max_p min(pa + (1-p)c, pb + (1-p)d)` over `p ∈ [0,1]`",
    game phrase!"lower value of the zero-sum game with payoffs $v$, $v$, $v$ and $v$" (fun a b c d => mx (mn a b) (mn c d))
      "`max(min(a,b), min(c,d))`, in pure strategies",
    game phrase!"upper value of the zero-sum game with payoffs $v$, $v$, $v$ and $v$" (fun a b c d => mn (mx a c) (mx b d))
      "`min(max(a,c), max(b,d))`, in pure strategies",
    { name := phrase!"expected payoff of the strategies $v$ and $v$ in the zero-sum game with payoffs $v$, $v$, $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real prob, dom1 .real prob, none, none, none, none],
      doc := "`pq a + p(1-q) b + (1-p)q c + (1-p)(1-q) d`",
      value := close <| lamT .real prob fun p => lamT .real prob fun q => lamR fun a => lamR fun b => lamR fun c => lamR fun d =>
        add (add (mul (mul p q) a) (mul (mul p (sub (num 1) q)) b))
          (add (mul (mul (sub (num 1) p) q) c) (mul (mul (sub (num 1) p) (sub (num 1) q)) d)) }]

end Leanify.Games
