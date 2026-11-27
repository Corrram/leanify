import Leanify.Library.Core

/-! # Vocabulary: self-similar fractals

The dimensions of self-similar sets and the measures of the stages of the classical
fractals (`We write $L_n$ for the length of the Koch curve after $n$ steps.`). The Cantor set
itself, as a set, is in the field `topology`.

* notions: the similarity dimension of a self-similar set made of `N` copies scaled by `r` (the
  `s` with `N r^s = 1`) and of a self-similar set with two ratios `r₁`, `r₂` (the `s` with
  `r₁^s + r₂^s = 1`, Moran's equation); the dimension of the middle-thirds Cantor set; the
  length and the number of intervals of the `n`th stage of the Cantor construction; the length
  of the Koch curve after `n` steps (from a unit segment) and the area of the Koch snowflake on
  a triangle with side `s`; the area of the Sierpinski triangle with side `s` after `n` steps;
  the volume of the Menger sponge after `n` steps (from a unit cube).

The similarity dimensions are terms of the core language; the other quantities are constants,
interpreted by the declarations of `Leanify/Library/FractalsModel.lean`: Mathlib's
`cantorSet`, `preCantorSet` and Hausdorff dimension `dimH`, the stages of the Koch curve and
snowflake as polygonal paths of `ℂ`, of the Sierpinski triangle and the Menger sponge as unions
of scaled copies, and their lengths and Lebesgue measures. The formulas (`log N / log(1/r)`,
`log 2 / log 3`, `(2/3)^n`, `2^n`, `(4/3)^n`, `2√3 s²/5`, `(√3/4) s² (3/4)^n`, `(20/27)^n`) are
theorems, not definitions. -/

namespace Leanify.Fractals
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def rpow (x s : B) : B := app2 (prim .rpow) x s
def log (x : B) : B := app (prim (.realFn .log)) x
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def ratio (r : B) : B := and (lt (num 0) r) (lt r (num 1))
def stage (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real natP], doc, value := .const c }

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def cantorDimension : Nat := 0
def cantorLength : Nat := 1
def cantorIntervals : Nat := 2
def kochLength : Nat := 3
def snowflakeArea : Nat := 4
def sierpinskiArea : Nat := 5
def mengerVolume : Nat := 6
end Const

def vocab : Vocab where
  consts := [.real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\dim_H C", w!"\\lambda(C_{#})", w!"\\#\\pi_0(C_{#})", w!"\\ell(K_{#})", w!"\\operatorname{area}(\\mathrm{Snow}_{#})",
    w!"\\operatorname{area}(\\mathrm{Sier}_{#1,#2})", w!"\\operatorname{vol}(\\mathrm{Menger}_{#})"]
  constLean := [w!"Leanify.Fractals.cantorDimension", w!"Leanify.Fractals.cantorLength", w!"Leanify.Fractals.cantorIntervals",
    w!"Leanify.Fractals.kochLength", w!"Leanify.Fractals.snowflakeArea", w!"Leanify.Fractals.sierpinskiArea",
    w!"Leanify.Fractals.mengerVolume"]
  modules := [w!"Leanify.Library.FractalsModel"]
  notions := [
    { name := phrase!"similarity dimension of a self-similar set with $v$ pieces scaled by $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => and (isInt n) (le (num 2) n), dom2 .real fun _ r => ratio r],
      doc := "the `s` with `N r^s = 1`: `N` copies of the set, each scaled by `0 < r < 1` (`log N / log(1/r)`)",
      value := close <| lamT .real (fun n => and (isInt n) (le (num 2) n)) fun n => lamT .real ratio fun r =>
        theR fun s => eq (mul n (rpow r s)) (num 1) },
    { name := phrase!"similarity dimension of a self-similar set with ratios $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real ratio, dom2 .real fun _ r => ratio r],
      doc := "the `s ≥ 0` with `r₁^s + r₂^s = 1` (Moran's equation), for `0 < r₁, r₂ < 1`",
      value := close <| lamT .real ratio fun a => lamT .real ratio fun b =>
        theR fun s => and (le (num 0) s) (eq (add (rpow a s) (rpow b s)) (num 1)) },
    { name := phrase!"dimension of the middle-thirds Cantor set", ty := .real,
      doc := "the Hausdorff dimension of Mathlib's `cantorSet` (`log 2 / log 3`)", value := .const Const.cantorDimension },
    stage phrase!"length of the Cantor set after $v$ steps" Const.cantorLength
      "the Lebesgue measure of the `n`th stage, Mathlib's `preCantorSet n` (`(2/3)^n`)",
    stage phrase!"number of intervals of the Cantor set after $v$ steps" Const.cantorIntervals
      "the connected components of the `n`th stage (`2^n`)",
    stage phrase!"length of the Koch curve after $v$ steps" Const.kochLength
      "the length of the polygonal path after `n` steps from a unit segment (`(4/3)^n`)",
    { name := phrase!"area of the Koch snowflake with side $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s],
      doc := "the Lebesgue measure of the snowflake on a triangle with side `s` (`2√3 s²/5`)", value := .const Const.snowflakeArea },
    { name := phrase!"area of the Sierpinski triangle with side $v$ after $v$ steps", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s, dom2 .real fun _ n => natP n],
      doc := "the Lebesgue measure of the `n`th stage (`(√3/4) s² (3/4)^n`)", value := .const Const.sierpinskiArea },
    stage phrase!"volume of the Menger sponge after $v$ steps" Const.mengerVolume
      "the Lebesgue measure of the `n`th stage from a unit cube (`(20/27)^n`)"]

end Leanify.Fractals
