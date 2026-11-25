import Leanify.Library.Core

/-! # Vocabulary: thermodynamics

The closed-form quantities of elementary thermodynamics and statistical mechanics, with the
constants of nature as arguments (`We write $\eta(T_h,T_c)$ for the Carnot efficiency between
the hot temperature $T_h$ and the cold temperature $T_c$.`).

* notions: the Carnot efficiency `1 - T_c/T_h` and the coefficient of performance
  `T_c/(T_h - T_c)` of a Carnot refrigerator; the pressure `nRT/V` of an ideal gas; the
  temperature `T_a + (T₀ - T_a)e^{-kt}` by Newton's law of cooling; the entropy change
  `C log(T₂/T₁)` of heating a heat capacity `C`; the power `σAT⁴` radiated by a black body; the
  Boltzmann factor `e^{-E/(kT)}`; the mean energy `ε/(e^{ε/(kT)} + 1)` of a two-level system.

Every meaning is a term of the core language. -/

namespace Leanify.Thermodynamics
open Build Core

def pos (x : B) : B := lt (num 0) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def carnot (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun h c => and (pos c) (lt c h)], doc,
    value := close <| lamT .real pos fun h => lamT .real (fun c => and (pos c) (lt c h)) fun c => body h c }
def three (name : Phrase) (d1 : B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ y => pos y, dom3 .real fun _ _ z => pos z], doc,
    value := close <| lamT .real d1 fun x => lamT .real pos fun y => lamT .real pos fun z => body x y z }

def vocab : Vocab where
  notions := [
    carnot phrase!"Carnot efficiency between the hot temperature $v$ and the cold temperature $v$" (fun h c => sub (num 1) (div c h))
      "`1 - T_c/T_h`, for `0 < T_c < T_h`",
    carnot phrase!"coefficient of performance of a Carnot refrigerator between the hot temperature $v$ and the cold temperature $v$"
      (fun h c => div c (sub h c)) "`T_c/(T_h - T_c)`",
    { name := phrase!"pressure of $v$ moles of an ideal gas at temperature $v$ in volume $v$ with gas constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ t => pos t, dom3 .real fun _ _ v => pos v, dom4 .real fun _ _ _ r => pos r],
      doc := "`nRT/V`",
      value := close <| lamT .real pos fun n => lamT .real pos fun t => lamT .real pos fun v => lamT .real pos fun r =>
        div (mul n (mul r t)) v },
    { name := phrase!"temperature at time $v$ by Newton's law of cooling with ambient temperature $v$, initial temperature $v$ and rate $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, none, none, dom4 .real fun _ _ _ k => pos k],
      doc := "`T_a + (T₀ - T_a)e^{-kt}`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamR fun a => lamR fun t0 => lamT .real pos fun k =>
        add a (mul (sub t0 a) (exp (neg (mul k t)))) },
    three phrase!"entropy change of heating the heat capacity $v$ from temperature $v$ to temperature $v$" pos
      (fun c a b => mul c (log (div b a))) "`C log(T₂/T₁)`, for a constant heat capacity `C`",
    three phrase!"power radiated by a black body with area $v$ at temperature $v$ with Stefan-Boltzmann constant $v$" pos
      (fun a t s => mul s (mul a (mul (mul t t) (mul t t)))) "`σAT⁴`",
    { name := phrase!"Boltzmann factor of the energy $v$ at temperature $v$ with Boltzmann constant $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ t => pos t, dom3 .real fun _ _ k => pos k],
      doc := "`e^{-E/(kT)}`",
      value := close <| lamR fun e => lamT .real pos fun t => lamT .real pos fun k => exp (neg (div e (mul k t))) },
    three phrase!"mean energy of a two-level system with gap $v$ at temperature $v$ with Boltzmann constant $v$" pos
      (fun g t k => div g (add (exp (div g (mul k t))) (num 1))) "`ε/(e^{ε/(kT)} + 1)`"]

end Leanify.Thermodynamics
