import Leanify.Library.Core

/-! # Vocabulary: pharmacokinetics

The one-compartment model with first-order elimination, by dose, volume and rates (`We write
$C(t,D,V,k)$ for the concentration at time $t$ after an intravenous dose $D$ with volume of
distribution $V$ and elimination rate $k$.`).

* notions: the concentration `(D/V)e^{-kt}` after an intravenous bolus; the clearance `kV`; the
  elimination half-life `V log 2/CL`; the area under the curve `D/CL`; the average steady-state
  concentration `FD/(CL τ)` of a dose `D` with bioavailability `F` every `τ`; the accumulation
  factor `1/(1 - e^{-kτ})`; the loading dose `C V/F` for a target concentration `C`.

Every meaning is a term of the core language. -/

namespace Leanify.Pharmacokinetics
open Build Core

def pos (x : B) : B := lt (num 0) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def frac (f : B) : B := and (lt (num 0) f) (le f (num 1))
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }

def vocab : Vocab where
  notions := [
    { name := phrase!"concentration at time $v$ after an intravenous dose $v$ with volume of distribution $v$ and elimination rate $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, dom2 .real fun _ d => le (num 0) d, dom3 .real fun _ _ v => pos v, dom4 .real fun _ _ _ k => pos k],
      doc := "`(D/V)e^{-kt}`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamT .real (fun d => le (num 0) d) fun d => lamT .real pos fun v =>
        lamT .real pos fun k => mul (div d v) (exp (neg (mul k t))) },
    two phrase!"clearance for the elimination rate $v$ and the volume of distribution $v$" (fun k v => mul k v) "`kV`",
    two phrase!"elimination half-life for the volume of distribution $v$ and the clearance $v$" (fun v c => div (mul v (log (num 2))) c)
      "`V log 2/CL`",
    { name := phrase!"area under the curve of the dose $v$ with clearance $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun d => le (num 0) d, dom2 .real fun _ c => pos c], doc := "`D/CL`",
      value := close <| lamT .real (fun d => le (num 0) d) fun d => lamT .real pos fun c => div d c },
    { name := phrase!"average steady-state concentration of the dose $v$ every $v$ with bioavailability $v$ and clearance $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun d => le (num 0) d, dom2 .real fun _ t => pos t, dom3 .real fun _ _ f => frac f, dom4 .real fun _ _ _ c => pos c],
      doc := "`FD/(CL τ)`",
      value := close <| lamT .real (fun d => le (num 0) d) fun d => lamT .real pos fun t => lamT .real frac fun f => lamT .real pos fun c =>
        div (mul f d) (mul c t) },
    two phrase!"accumulation factor for the elimination rate $v$ and the dosing interval $v$"
      (fun k t => div (num 1) (sub (num 1) (exp (neg (mul k t))))) "`1/(1 - e^{-kτ})`",
    { name := phrase!"loading dose for the target concentration $v$ with volume of distribution $v$ and bioavailability $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun c => le (num 0) c, dom2 .real fun _ v => pos v, dom3 .real fun _ _ f => frac f], doc := "`CV/F`",
      value := close <| lamT .real (fun c => le (num 0) c) fun c => lamT .real pos fun v => lamT .real frac fun f => div (mul c v) f }]

end Leanify.Pharmacokinetics
