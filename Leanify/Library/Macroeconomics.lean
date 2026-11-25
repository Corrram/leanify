import Leanify.Library.Core

/-! # Vocabulary: macroeconomics

Growth models, multipliers and policy rules, by their parameters (`We write $k(s,n,d,a)$ for the
steady-state capital per worker of the Solow model with saving rate $s$, population growth $n$,
depreciation $d$ and capital share $a$.`). Elasticities and production functions are in the
field `economics`, interest and annuities in `finance`.

* notions: the steady-state capital `(s/(n+δ))^{1/(1-α)}` and output `(s/(n+δ))^{α/(1-α)}` per
  worker of the Solow model, and its golden-rule saving rate `α`; the Harrod–Domar growth rate
  `s/v`; the real interest rate `(1+i)/(1+π) - 1` (Fisher); the compound annual growth rate
  `(b/a)^{1/n} - 1`; the money multiplier `1/r` and the Keynesian multiplier `1/(1-c)`; the
  Taylor rule rate `r* + π + (π - π*)/2 + y/2`.

Every meaning is a term of the core language. -/

namespace Leanify.Macroeconomics
open Build Core

def pos (x : B) : B := lt (num 0) x
def unit (x : B) : B := and (lt (num 0) x) (lt x (num 1))
def rpow (x s : B) : B := app2 (prim .rpow) x s
def solow (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real unit, none, dom3 .real fun _ n d => lt (num 0) (add n d), dom4 .real fun _ _ _ a => unit a], doc,
    value := close <| lamT .real unit fun s => lamR fun n => lamT .real (fun d => lt (num 0) (add n d)) fun d => lamT .real unit fun a => body s n d a }

def vocab : Vocab where
  notions := [
    solow phrase!"steady-state capital per worker of the Solow model with saving rate $v$, population growth $v$, depreciation $v$ and capital share $v$"
      (fun s n d a => rpow (div s (add n d)) (div (num 1) (sub (num 1) a))) "`(s/(n+δ))^{1/(1-α)}`",
    solow phrase!"steady-state output per worker of the Solow model with saving rate $v$, population growth $v$, depreciation $v$ and capital share $v$"
      (fun s n d a => rpow (div s (add n d)) (div a (sub (num 1) a))) "`(s/(n+δ))^{α/(1-α)}`",
    { name := phrase!"golden-rule saving rate of the Solow model with capital share $v$", ty := .real ⟶ .real, doms := [dom1 .real unit],
      doc := "`α`: the saving rate that maximizes steady-state consumption", value := close <| lamT .real unit fun a => a },
    { name := phrase!"Harrod-Domar growth rate for the saving rate $v$ and the capital-output ratio $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ v => pos v], doc := "`s/v`",
      value := close <| lamR fun s => lamT .real pos fun v => div s v },
    { name := phrase!"real interest rate for the nominal rate $v$ and the inflation rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ p => lt (neg (num 1)) p], doc := "`(1+i)/(1+π) - 1` (Fisher equation)",
      value := close <| lamR fun i => lamT .real (fun p => lt (neg (num 1)) p) fun p => sub (div (add (num 1) i) (add (num 1) p)) (num 1) },
    { name := phrase!"compound annual growth rate from $v$ to $v$ over $v$ years", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ b => pos b, dom3 .real fun _ _ n => pos n], doc := "`(b/a)^{1/n} - 1`",
      value := close <| lamT .real pos fun a => lamT .real pos fun b => lamT .real pos fun n => sub (rpow (div b a) (div (num 1) n)) (num 1) },
    { name := phrase!"money multiplier for the reserve ratio $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun r => and (lt (num 0) r) (le r (num 1))], doc := "`1/r`",
      value := close <| lamT .real (fun r => and (lt (num 0) r) (le r (num 1))) fun r => div (num 1) r },
    { name := phrase!"Keynesian multiplier for the marginal propensity to consume $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun c => and (le (num 0) c) (lt c (num 1))], doc := "`1/(1-c)`",
      value := close <| lamT .real (fun c => and (le (num 0) c) (lt c (num 1))) fun c => div (num 1) (sub (num 1) c) },
    { name := phrase!"Taylor rule rate for the inflation $v$, the target inflation $v$, the output gap $v$ and the neutral real rate $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`r* + π + (π - π*)/2 + y/2`",
      value := close <| lamR fun p => lamR fun t => lamR fun y => lamR fun r =>
        add (add r p) (add (div (sub p t) (num 2)) (div y (num 2))) }]

end Leanify.Macroeconomics
