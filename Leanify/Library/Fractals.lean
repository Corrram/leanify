import Leanify.Library.Core

/-! # Vocabulary: self-similar fractals

The dimensions of self-similar sets and the measures of the stages of the classical
fractals (`We write $L_n$ for the length of the Koch curve after $n$ steps.`). The Cantor set
itself, as a set, is in the field `topology`.

* notions: the similarity dimension `log N / log(1/r)` of a self-similar set made of `N` copies
  scaled by `r`; the similarity dimension of a self-similar set with two ratios `r₁`, `r₂`
  (the `s` with `r₁^s + r₂^s = 1`, Moran's equation); the dimension `log 2 / log 3` of the
  middle-thirds Cantor set; the length `(2/3)^n` and the number `2^n` of intervals of the
  `n`th stage of the Cantor construction; the length `(4/3)^n` of the Koch curve after `n`
  steps (from a unit segment) and the area `2√3 s²/5` of the Koch snowflake on a triangle with
  side `s`; the area `(√3/4) s² (3/4)^n` of the Sierpinski triangle with side `s` after `n`
  steps; the volume `(20/27)^n` of the Menger sponge after `n` steps (from a unit cube).

Every meaning is a term of the core language. -/

namespace Leanify.Fractals
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def rpow (x s : B) : B := app2 (prim .rpow) x s
def log (x : B) : B := app (prim (.realFn .log)) x
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def ratio (r : B) : B := and (lt (num 0) r) (lt r (num 1))
def stage (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real natP], doc, value := close <| lamT .real natP body }

def vocab : Vocab where
  notions := [
    { name := phrase!"similarity dimension of a self-similar set with $v$ pieces scaled by $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => and (isInt n) (le (num 2) n), dom2 .real fun _ r => ratio r],
      doc := "`log N / log(1/r)`: `N` copies of the set, each scaled by `0 < r < 1`",
      value := close <| lamT .real (fun n => and (isInt n) (le (num 2) n)) fun n => lamT .real ratio fun r =>
        div (log n) (log (div (num 1) r)) },
    { name := phrase!"similarity dimension of a self-similar set with ratios $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real ratio, dom2 .real fun _ r => ratio r],
      doc := "the `s ≥ 0` with `r₁^s + r₂^s = 1` (Moran's equation), for `0 < r₁, r₂ < 1`",
      value := close <| lamT .real ratio fun a => lamT .real ratio fun b =>
        theR fun s => and (le (num 0) s) (eq (add (rpow a s) (rpow b s)) (num 1)) },
    { name := phrase!"dimension of the middle-thirds Cantor set", ty := .real,
      doc := "`log 2 / log 3`", value := close <| div (log (num 2)) (log (num 3)) },
    stage phrase!"length of the Cantor set after $v$ steps" (fun n => zpow (div (num 2) (num 3)) n)
      "`(2/3)^n`: the total length of the `n`th stage, from `[0,1]`",
    stage phrase!"number of intervals of the Cantor set after $v$ steps" (fun n => zpow (num 2) n) "`2^n`",
    stage phrase!"length of the Koch curve after $v$ steps" (fun n => zpow (div (num 4) (num 3)) n)
      "`(4/3)^n`, from a unit segment",
    { name := phrase!"area of the Koch snowflake with side $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s],
      doc := "`2√3 s²/5`: the limit of the areas of the snowflake stages on a triangle with side `s`",
      value := close <| lamT .real (fun s => lt (num 0) s) fun s => div (mul (mul (num 2) (sqrt (num 3))) (mul s s)) (num 5) },
    { name := phrase!"area of the Sierpinski triangle with side $v$ after $v$ steps", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s, dom2 .real fun _ n => natP n],
      doc := "`(√3/4) s² (3/4)^n`",
      value := close <| lamT .real (fun s => lt (num 0) s) fun s => lamT .real natP fun n =>
        mul (div (mul (sqrt (num 3)) (mul s s)) (num 4)) (zpow (div (num 3) (num 4)) n) },
    stage phrase!"volume of the Menger sponge after $v$ steps" (fun n => zpow (div (num 20) (num 27)) n)
      "`(20/27)^n`, from a unit cube"]

end Leanify.Fractals
