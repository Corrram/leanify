import Leanify.Library.Core

/-! # Vocabulary: electric circuits

The closed-form quantities of resistor, capacitor and inductor circuits, by their parameters
(`We write $\tau(R,C)$ for the time constant of the RC circuit with resistance $R$ and
capacitance $C$.`).

* notions: the resistance `R₁ + R₂` of two resistances in series and `R₁R₂/(R₁ + R₂)` in
  parallel; the power `V²/R` dissipated by a resistance at a voltage; the time constant `RC`
  and the capacitor voltage `V(1 - e^{-t/(RC)})` of an RC circuit charged from a source; the
  energies `CV²/2` in a capacitance and `LI²/2` in an inductance; the resonant frequency
  `1/(2π√(LC))` of an LC circuit; the impedance `√(R² + (ωL - 1/(ωC))²)` and the quality
  factor `√(L/C)/R` of a series RLC circuit.

Every meaning is a term of the core language. -/

namespace Leanify.Circuits
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def exp (x : B) : B := app (prim (.realFn .exp)) x
def pi : B := prim .pi
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }
def posAny (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, none], doc,
    value := close <| lamT .real pos fun x => lamR fun y => body x y }

def vocab : Vocab where
  notions := [
    two phrase!"resistance of $v$ and $v$ in series" (fun a b => add a b) "`R₁ + R₂`",
    two phrase!"resistance of $v$ and $v$ in parallel" (fun a b => div (mul a b) (add a b)) "`R₁R₂/(R₁ + R₂)`",
    posAny phrase!"power dissipated by the resistance $v$ at the voltage $v$" (fun r v => div (mul v v) r) "`V²/R`",
    two phrase!"time constant of the RC circuit with resistance $v$ and capacitance $v$" (fun r c => mul r c) "`RC`",
    { name := phrase!"capacitor voltage at time $v$ in the RC circuit with resistance $v$, capacitance $v$ and source voltage $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, dom2 .real fun _ r => pos r, dom3 .real fun _ _ c => pos c, none],
      doc := "`V(1 - e^{-t/(RC)})`, charging from `0`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamT .real pos fun r => lamT .real pos fun c => lamR fun v =>
        mul v (sub (num 1) (exp (neg (div t (mul r c))))) },
    posAny phrase!"energy stored in the capacitance $v$ at the voltage $v$" (fun c v => div (mul c (mul v v)) (num 2)) "`CV²/2`",
    posAny phrase!"energy stored in the inductance $v$ with the current $v$" (fun l i => div (mul l (mul i i)) (num 2)) "`LI²/2`",
    two phrase!"resonant frequency of the LC circuit with inductance $v$ and capacitance $v$"
      (fun l c => div (num 1) (mul (mul (num 2) pi) (sqrt (mul l c)))) "`1/(2π√(LC))`",
    { name := phrase!"impedance of the series RLC circuit with resistance $v$, inductance $v$ and capacitance $v$ at angular frequency $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r, dom2 .real fun _ l => pos l, dom3 .real fun _ _ c => pos c, dom4 .real fun _ _ _ w => pos w],
      doc := "`√(R² + (ωL - 1/(ωC))²)`",
      value := close <| lamT .real (fun r => le (num 0) r) fun r => lamT .real pos fun l => lamT .real pos fun c => lamT .real pos fun w =>
        sqrt (add (mul r r) (mul (sub (mul w l) (div (num 1) (mul w c))) (sub (mul w l) (div (num 1) (mul w c))))) },
    { name := phrase!"quality factor of the series RLC circuit with resistance $v$, inductance $v$ and capacitance $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ l => pos l, dom3 .real fun _ _ c => pos c],
      doc := "`√(L/C)/R`",
      value := close <| lamT .real pos fun r => lamT .real pos fun l => lamT .real pos fun c => div (sqrt (div l c)) r }]

end Leanify.Circuits
