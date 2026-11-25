import Leanify.Library.Core

/-! # Vocabulary: population dynamics

The closed forms of the classical population models, by their parameters (`We write $N(t)$
for the logistic population at time $t$ with growth rate $r$, carrying capacity $K$ and
initial size $N_0$.`). Epidemic models are in the field `epidemics`.

* notions: the exponential population `N₀e^{rt}` and its doubling time `log 2/r`; the logistic
  population `K N₀ e^{rt}/(K + N₀(e^{rt} - 1))`, the maximum sustainable yield `rK/4` and the
  equilibrium `K(1 - E/r)` under harvesting effort `E < r`; the next generation of the Ricker
  map `N e^{r(1 - N/K)}` and of the Beverton–Holt map `RN/(1 + (R-1)N/K)`; the prey equilibrium
  `γ/δ` and the predator equilibrium `α/β` of the Lotka–Volterra system `x' = αx - βxy`,
  `y' = δxy - γy`.

Every meaning is a term of the core language. -/

namespace Leanify.PopulationDynamics
open Build Core

def pos (x : B) : B := lt (num 0) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }
def three (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ y => pos y, dom3 .real fun _ _ z => le (num 0) z], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => lamT .real (fun z => le (num 0) z) fun z => body x y z }
def lv (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ b => pos b, dom3 .real fun _ _ c => pos c, dom4 .real fun _ _ _ d => pos d], doc,
    value := close <| lamT .real pos fun a => lamT .real pos fun b => lamT .real pos fun c => lamT .real pos fun d => body a b c d }

def vocab : Vocab where
  notions := [
    { name := phrase!"exponential population at time $v$ with growth rate $v$ and initial size $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun _ _ n => pos n], doc := "`N₀ e^{rt}`",
      value := close <| lamR fun t => lamR fun r => lamT .real pos fun n => mul n (exp (mul r t)) },
    { name := phrase!"doubling time for the growth rate $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`log 2 / r`", value := close <| lamT .real pos fun r => div (log (num 2)) r },
    { name := phrase!"logistic population at time $v$ with growth rate $v$, carrying capacity $v$ and initial size $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, dom2 .real fun _ r => pos r, dom3 .real fun _ _ k => pos k, dom4 .real fun _ _ _ n => pos n],
      doc := "`K N₀ e^{rt}/(K + N₀(e^{rt} - 1))`: the solution of `N' = rN(1 - N/K)`, `N(0) = N₀`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamT .real pos fun r => lamT .real pos fun k => lamT .real pos fun n =>
        div (mul (mul k n) (exp (mul r t))) (add k (mul n (sub (exp (mul r t)) (num 1)))) },
    two phrase!"maximum sustainable yield for growth rate $v$ and carrying capacity $v$" (fun r k => div (mul r k) (num 4))
      "`rK/4`: the largest harvest `rN(1 - N/K)`, at `N = K/2`",
    { name := phrase!"equilibrium of the logistic model with growth rate $v$, carrying capacity $v$ and harvesting effort $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ k => pos k, dom3 .real fun r _ e => and (le (num 0) e) (lt e r)],
      doc := "`K(1 - E/r)`: the positive equilibrium of `N' = rN(1 - N/K) - EN`, for `0 ≤ E < r`",
      value := close <| lamT .real pos fun r => lamT .real pos fun k => lamT .real (fun e => and (le (num 0) e) (lt e r)) fun e =>
        mul k (sub (num 1) (div e r)) },
    three phrase!"Ricker map with growth rate $v$ and carrying capacity $v$ at $v$"
      (fun r k n => mul n (exp (mul r (sub (num 1) (div n k))))) "`N e^{r(1 - N/K)}`",
    three phrase!"Beverton-Holt map with growth rate $v$ and carrying capacity $v$ at $v$"
      (fun r k n => div (mul r n) (add (num 1) (div (mul (sub r (num 1)) n) k))) "`RN/(1 + (R-1)N/K)`",
    lv phrase!"prey equilibrium of the Lotka-Volterra system with rates $v$, $v$, $v$ and $v$" (fun _ _ c d => div c d)
      "`γ/δ` for `x' = αx - βxy`, `y' = δxy - γy` with the rates `α`, `β`, `γ`, `δ`",
    lv phrase!"predator equilibrium of the Lotka-Volterra system with rates $v$, $v$, $v$ and $v$" (fun a b _ _ => div a b)
      "`α/β` for `x' = αx - βxy`, `y' = δxy - γy` with the rates `α`, `β`, `γ`, `δ`"]

end Leanify.PopulationDynamics
