import Leanify.Library.Core

/-! # Vocabulary: special relativity

The kinematics of special relativity, with the speed of light as an argument (`We write
$\gamma(v,c)$ for the Lorentz factor of the speed $v$ with the speed of light $c$.`).

* notions: the Lorentz factor `1/√(1 - v²/c²)` of a speed `|v| < c`; the rapidity
  `artanh(v/c) = ½ log((c+v)/(c-v))`; the relativistic sum `(u + v)/(1 + uv/c²)` of two
  velocities; the dilated time `γτ` of a proper time `τ` and the contracted length `L/γ` of a
  proper length `L`; the energy `γmc²` and the momentum `γmv` of a mass `m` at speed `v`, and
  its rest energy `mc²`; the redshift factor `√((c+v)/(c-v))` of a source receding at speed `v`.

Every meaning is a term of the core language. -/

namespace Leanify.Relativity
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def log (x : B) : B := app (prim (.realFn .log)) x
def gam (v c : B) : B := div (num 1) (sqrt (sub (num 1) (div (mul v v) (mul c c))))
/-- `|v| < c`, as a domain of `v` given `c`. -/
def sub1 (c v : B) : B := lt (abs v) c
/-- A notion of a speed and the speed of light: the speed's domain speaks about `c`, which
comes after it, so the value takes `c` first and the domains are checked when `c` is known. -/
def speed (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [none, dom2 .real fun v c => and (pos c) (sub1 c v)], doc,
    value := close <| lamR fun v => lamT .real (fun c => and (pos c) (sub1 c v)) fun c => body v c }
/-- A notion of a quantity, a speed and the speed of light. -/
def withQ (name : Phrase) (q : B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real q, none, dom3 .real fun _ v c => and (pos c) (sub1 c v)], doc,
    value := close <| lamT .real q fun x => lamR fun v => lamT .real (fun c => and (pos c) (sub1 c v)) fun c => body x v c }

def vocab : Vocab where
  notions := [
    speed phrase!"Lorentz factor of the speed $v$ with the speed of light $v$" gam "`1/√(1 - v²/c²)`, for `|v| < c`",
    speed phrase!"rapidity of the speed $v$ with the speed of light $v$"
      (fun v c => div (log (div (add c v) (sub c v))) (num 2)) "`artanh(v/c) = ½ log((c+v)/(c-v))`",
    speed phrase!"redshift factor of the speed $v$ with the speed of light $v$"
      (fun v c => sqrt (div (add c v) (sub c v))) "`√((c+v)/(c-v))`: the ratio of received to emitted wavelength, source receding at `v`",
    { name := phrase!"relativistic sum of the velocities $v$ and $v$ with the speed of light $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun u v c => and (pos c) (and (sub1 c u) (sub1 c v))],
      doc := "`(u + v)/(1 + uv/c²)`, for `|u|, |v| < c`",
      value := close <| lamR fun u => lamR fun v => lamT .real (fun c => and (pos c) (and (sub1 c u) (sub1 c v))) fun c =>
        div (add u v) (add (num 1) (div (mul u v) (mul c c))) },
    withQ phrase!"dilated time of the proper time $v$ at the speed $v$ with the speed of light $v$" (fun t => le (num 0) t)
      (fun t v c => mul (gam v c) t) "`γτ`",
    withQ phrase!"contracted length of the proper length $v$ at the speed $v$ with the speed of light $v$" (fun l => le (num 0) l)
      (fun l v c => div l (gam v c)) "`L/γ`",
    withQ phrase!"relativistic energy of the mass $v$ at the speed $v$ with the speed of light $v$" pos
      (fun m v c => mul (gam v c) (mul m (mul c c))) "`γmc²`",
    withQ phrase!"relativistic momentum of the mass $v$ at the speed $v$ with the speed of light $v$" pos
      (fun m v c => mul (gam v c) (mul m v)) "`γmv`",
    { name := phrase!"rest energy of the mass $v$ with the speed of light $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ c => pos c], doc := "`mc²`",
      value := close <| lamT .real pos fun m => lamT .real pos fun c => mul m (mul c c) }]

end Leanify.Relativity
