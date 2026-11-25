import Leanify.Library.Core

/-! # Vocabulary: chemical kinetics

Concentrations, half-lives and rates of elementary reactions, by their parameters (`We write
$c(t)$ for the concentration at time $t$ in a first-order reaction with rate constant $k$ and
initial concentration $c_0$.`).

* notions: the concentration at time `t` in a reaction of order zero (`max(c₀ - kt, 0)`), one
  (`c₀e^{-kt}`) and two (`c₀/(1 + kc₀t)`); the half-life `log 2/k` of a first-order and `1/(kc₀)`
  of a second-order reaction, and the decay constant `log 2/T` of a half-life `T`; the Arrhenius
  rate constant `A e^{-E_a/(RT)}`; the Michaelis–Menten rate `V_max S/(K_M + S)`; the pH
  `-log₁₀ [H⁺]`.

Every meaning is a term of the core language. -/

namespace Leanify.Kinetics
open Build Core

def pos (x : B) : B := lt (num 0) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def reaction (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real fun t => le (num 0) t, dom2 .real fun _ k => pos k, dom3 .real fun _ _ c => pos c], doc,
    value := close <| lamT .real (fun t => le (num 0) t) fun t => lamT .real pos fun k => lamT .real pos fun c => body t k c }
def one (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := close <| lamT .real pos body }

def vocab : Vocab where
  notions := [
    reaction phrase!"concentration at time $v$ in a zeroth-order reaction with rate constant $v$ and initial concentration $v$"
      (fun t k c => app2 (prim .max) (sub c (mul k t)) (num 0)) "`max(c₀ - kt, 0)`",
    reaction phrase!"concentration at time $v$ in a first-order reaction with rate constant $v$ and initial concentration $v$"
      (fun t k c => mul c (exp (neg (mul k t)))) "`c₀e^{-kt}`",
    reaction phrase!"concentration at time $v$ in a second-order reaction with rate constant $v$ and initial concentration $v$"
      (fun t k c => div c (add (num 1) (mul k (mul c t)))) "`c₀/(1 + kc₀t)`",
    one phrase!"half-life of a first-order reaction with rate constant $v$" (fun k => div (log (num 2)) k) "`log 2/k`",
    { name := phrase!"half-life of a second-order reaction with rate constant $v$ and initial concentration $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ c => pos c], doc := "`1/(kc₀)`",
      value := close <| lamT .real pos fun k => lamT .real pos fun c => div (num 1) (mul k c) },
    one phrase!"decay constant for the half-life $v$" (fun t => div (log (num 2)) t) "`log 2/T`",
    { name := phrase!"Arrhenius rate constant for the prefactor $v$, the activation energy $v$ and the temperature $v$ with gas constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ e => le (num 0) e, dom3 .real fun _ _ t => pos t, dom4 .real fun _ _ _ r => pos r],
      doc := "`A e^{-E_a/(RT)}`",
      value := close <| lamT .real pos fun a => lamT .real (fun e => le (num 0) e) fun e => lamT .real pos fun t => lamT .real pos fun r =>
        mul a (exp (neg (div e (mul r t)))) },
    { name := phrase!"Michaelis-Menten rate for the maximal rate $v$, the Michaelis constant $v$ and the substrate concentration $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ k => pos k, dom3 .real fun _ _ s => le (num 0) s],
      doc := "`V_max S/(K_M + S)`",
      value := close <| lamT .real pos fun v => lamT .real pos fun k => lamT .real (fun s => le (num 0) s) fun s => div (mul v s) (add k s) },
    one phrase!"pH for the hydrogen ion concentration $v$" (fun h => neg (div (log h) (log (num 10)))) "`-log₁₀ [H⁺]`"]

end Leanify.Kinetics
