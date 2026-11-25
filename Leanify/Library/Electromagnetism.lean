import Leanify.Library.Core

/-! # Vocabulary: electromagnetism

The fields and forces of point charges, wires and plates, with the constants of nature as
arguments (`We write $F(a,b,r,k)$ for the Coulomb force between the
charges $a$ and $b$ at distance $r$ with Coulomb constant $k$.`).

* notions: the Coulomb force `kq₁q₂/r²` (positive for repulsion), the field `kq/r²` and the
  potential `kq/r` of a point charge; the capacitance `εA/d` of a parallel-plate capacitor and
  the energy density `εE²/2` of an electric field; the magnetic field `μI/(2πr)` of a long
  straight wire and `μnI` inside a long solenoid; the magnetic force `|q|vB sin θ` on a moving
  charge, its cyclotron frequency `|q|B/(2πm)` and its Larmor radius `mv/(|q|B)`.

Every meaning is a term of the core language. -/

namespace Leanify.Electromagnetism
open Build Core

def pos (x : B) : B := lt (num 0) x
def sin (x : B) : B := app (prim (.realFn .sin)) x
def pi : B := prim .pi
def nz (x : B) : B := ne x (num 0)
def point (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [none, dom2 .real fun _ r => pos r, dom3 .real fun _ _ k => pos k], doc,
    value := close <| lamR fun q => lamT .real pos fun r => lamT .real pos fun k => body q r k }
def three (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y, dom3 .real fun _ _ z => pos z], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => lamT .real pos fun z => body x y z }

def vocab : Vocab where
  notions := [
    { name := phrase!"Coulomb force between the charges $v$ and $v$ at distance $v$ with Coulomb constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun _ _ r => pos r, dom4 .real fun _ _ _ k => pos k],
      doc := "`kq₁q₂/r²`, positive for repulsion",
      value := close <| lamR fun a => lamR fun b => lamT .real pos fun r => lamT .real pos fun k => div (mul k (mul a b)) (mul r r) },
    point phrase!"electric field of the point charge $v$ at distance $v$ with Coulomb constant $v$"
      (fun q r k => div (mul k q) (mul r r)) "`kq/r²`, the radial component",
    point phrase!"electric potential of the point charge $v$ at distance $v$ with Coulomb constant $v$"
      (fun q r k => div (mul k q) r) "`kq/r`",
    three phrase!"capacitance of a parallel-plate capacitor with area $v$ and separation $v$ with permittivity $v$"
      (fun a d e => div (mul e a) d) "`εA/d`",
    { name := phrase!"energy density of the electric field $v$ with permittivity $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ e => pos e], doc := "`εE²/2`",
      value := close <| lamR fun f => lamT .real pos fun e => div (mul e (mul f f)) (num 2) },
    { name := phrase!"magnetic field of a long wire with current $v$ at distance $v$ with permeability $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ r => pos r, dom3 .real fun _ _ m => pos m], doc := "`μI/(2πr)`",
      value := close <| lamR fun i => lamT .real pos fun r => lamT .real pos fun m => div (mul m i) (mul (mul (num 2) pi) r) },
    { name := phrase!"magnetic field inside a solenoid with $v$ turns per unit length and current $v$ with permeability $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none, dom3 .real fun _ _ m => pos m], doc := "`μnI`",
      value := close <| lamT .real pos fun n => lamR fun i => lamT .real pos fun m => mul m (mul n i) },
    { name := phrase!"magnetic force on the charge $v$ with speed $v$ at angle $v$ to the field $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ v => le (num 0) v, dom3 .real fun _ _ t => and (le (num 0) t) (le t pi), dom4 .real fun _ _ _ b => le (num 0) b],
      doc := "`|q|vB sin θ`",
      value := close <| lamR fun q => lamT .real (fun v => le (num 0) v) fun v => lamT .real (fun t => and (le (num 0) t) (le t pi)) fun t =>
        lamT .real (fun b => le (num 0) b) fun b => mul (abs q) (mul v (mul b (sin t))) },
    { name := phrase!"cyclotron frequency of the charge $v$ with mass $v$ in the field $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nz, dom2 .real fun _ m => pos m, dom3 .real fun _ _ b => pos b], doc := "`|q|B/(2πm)`",
      value := close <| lamT .real nz fun q => lamT .real pos fun m => lamT .real pos fun b => div (mul (abs q) b) (mul (mul (num 2) pi) m) },
    { name := phrase!"Larmor radius of the charge $v$ with mass $v$ and speed $v$ in the field $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nz, dom2 .real fun _ m => pos m, dom3 .real fun _ _ v => le (num 0) v, dom4 .real fun _ _ _ b => pos b],
      doc := "`mv/(|q|B)`",
      value := close <| lamT .real nz fun q => lamT .real pos fun m => lamT .real (fun v => le (num 0) v) fun v => lamT .real pos fun b =>
        div (mul m v) (mul (abs q) b) }]

end Leanify.Electromagnetism
