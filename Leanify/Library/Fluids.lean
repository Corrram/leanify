import Leanify.Library.Core

/-! # Vocabulary: fluid mechanics

The dimensionless numbers and closed-form flows of elementary fluid mechanics, by their
parameters (`We write $R(\rho,u,L,\mu)$ for the Reynolds number for
density $\rho$, speed $u$, length $L$ and viscosity $\mu$.`).

* notions: the Reynolds number `ρuL/μ` and the Froude number `u/√(gL)`; the hydrostatic
  pressure `p₀ + ρgh`; the speed `√(2gh)` of efflux from a depth `h` (Torricelli); the
  Hagen–Poiseuille flow rate `πr⁴Δp/(8μL)` through a pipe; the drag force `ρu²C_dA/2`; the
  Stokes terminal velocity `2(ρ_p - ρ_f)gr²/(9μ)` of a sphere; the dynamic pressure `ρu²/2`.

Every meaning is a term of the core language. -/

namespace Leanify.Fluids
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def pi : B := prim .pi
/-- The domain of a fifth argument (as `dom4` for the fourth). -/
def dom5 (t : Ty) (p : B → B → B → B → B → B) : Option Tm :=
  match close (lamR fun a => lamR fun b => lamR fun c => lamR fun d => lamR fun _ =>
      lamT t (fun _ => tt) fun self => p a b c d self) with
  | .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ inner)))) => some inner
  | _ => none
def four (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ b => le (num 0) b, dom3 .real fun _ _ c => pos c, dom4 .real fun _ _ _ d => pos d], doc,
    value := close <| lamT .real pos fun a => lamT .real (fun b => le (num 0) b) fun b => lamT .real pos fun c => lamT .real pos fun d => body a b c d }

def vocab : Vocab where
  notions := [
    four phrase!"Reynolds number for density $v$, speed $v$, length $v$ and viscosity $v$"
      (fun r u l m => div (mul r (mul u l)) m) "`ρuL/μ`",
    { name := phrase!"Froude number for speed $v$, length $v$ and gravity $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun u => le (num 0) u, dom2 .real fun _ l => pos l, dom3 .real fun _ _ g => pos g],
      doc := "`u/√(gL)`",
      value := close <| lamT .real (fun u => le (num 0) u) fun u => lamT .real pos fun l => lamT .real pos fun g => div u (sqrt (mul g l)) },
    { name := phrase!"hydrostatic pressure at depth $v$ with surface pressure $v$, density $v$ and gravity $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun h => le (num 0) h, none, dom3 .real fun _ _ r => pos r, dom4 .real fun _ _ _ g => pos g],
      doc := "`p₀ + ρgh`",
      value := close <| lamT .real (fun h => le (num 0) h) fun h => lamR fun p => lamT .real pos fun r => lamT .real pos fun g =>
        add p (mul r (mul g h)) },
    { name := phrase!"efflux speed from depth $v$ under gravity $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun h => le (num 0) h, dom2 .real fun _ g => pos g],
      doc := "`√(2gh)` (Torricelli's law)",
      value := close <| lamT .real (fun h => le (num 0) h) fun h => lamT .real pos fun g => sqrt (mul (num 2) (mul g h)) },
    four phrase!"Poiseuille flow rate through a pipe of radius $v$ with pressure drop $v$, viscosity $v$ and length $v$"
      (fun r p m l => div (mul pi (mul (mul (mul r r) (mul r r)) p)) (mul (num 8) (mul m l))) "`πr⁴Δp/(8μL)`",
    four phrase!"drag force for density $v$, speed $v$, drag coefficient $v$ and area $v$"
      (fun r u c a => div (mul r (mul (mul u u) (mul c a))) (num 2)) "`ρu²C_dA/2`",
    { name := phrase!"Stokes terminal velocity of a sphere of radius $v$ and density $v$ in a fluid of density $v$ and viscosity $v$ under gravity $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ p => pos p, dom3 .real fun _ _ f => pos f, dom4 .real fun _ _ _ m => pos m,
        dom5 .real fun _ _ _ _ g => pos g],
      doc := "`2(ρ_p - ρ_f)gr²/(9μ)`, for slow flow",
      value := close <| lamT .real pos fun r => lamT .real pos fun p => lamT .real pos fun f => lamT .real pos fun m => lamT .real pos fun g =>
        div (mul (mul (num 2) (sub p f)) (mul g (mul r r))) (mul (num 9) m) },
    { name := phrase!"dynamic pressure for density $v$ and speed $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none], doc := "`ρu²/2`",
      value := close <| lamT .real pos fun r => lamR fun u => div (mul r (mul u u)) (num 2) }]

end Leanify.Fluids
