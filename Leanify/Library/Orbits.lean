import Leanify.Library.Core

/-! # Vocabulary: orbital mechanics

Keplerian orbits and transfers, for the gravitational parameter `μ = GM` (`We write $v(r,a,\mu)$
for the orbital speed at distance $r$ on an orbit with semi-major axis $a$ for the gravitational
parameter $\mu$.`). Circular speeds, escape velocities and Kepler's third law are in the field
`mechanics`.

* notions: the speed `√(μ(2/r - 1/a))` (vis-viva); the periapsis `a(1-e)` and apoapsis `a(1+e)`
  distances; the specific orbital energy `-μ/(2a)`; the two burns
  `√(μ/r₁)(√(2r₂/(r₁+r₂)) - 1)` and `√(μ/r₂)(1 - √(2r₁/(r₁+r₂)))` of a Hohmann transfer from
  radius `r₁` to `r₂`; the synodic period `1/|1/T₁ - 1/T₂|`; the Hill radius `a(m/(3M))^{1/3}`.

Every meaning is a term of the core language. -/

namespace Leanify.Orbits
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def cbrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 3))
def ecc (e : B) : B := and (le (num 0) e) (lt e (num 1))
def hohmann (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ b => pos b, dom3 .real fun _ _ m => pos m], doc,
    value := close <| lamT .real pos fun a => lamT .real pos fun b => lamT .real pos fun m => body a b m }

def vocab : Vocab where
  notions := [
    { name := phrase!"orbital speed at distance $v$ on an orbit with semi-major axis $v$ for the gravitational parameter $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun r a => and (pos a) (le r (mul (num 2) a)), dom3 .real fun _ _ m => pos m],
      doc := "`√(μ(2/r - 1/a))` (vis-viva equation), for `r ≤ 2a`",
      value := close <| lamT .real pos fun r => lamT .real (fun a => and (pos a) (le r (mul (num 2) a))) fun a => lamT .real pos fun m =>
        sqrt (mul m (sub (div (num 2) r) (div (num 1) a))) },
    { name := phrase!"periapsis distance of an orbit with semi-major axis $v$ and eccentricity $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ e => ecc e], doc := "`a(1-e)`",
      value := close <| lamT .real pos fun a => lamT .real ecc fun e => mul a (sub (num 1) e) },
    { name := phrase!"apoapsis distance of an orbit with semi-major axis $v$ and eccentricity $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ e => ecc e], doc := "`a(1+e)`",
      value := close <| lamT .real pos fun a => lamT .real ecc fun e => mul a (add (num 1) e) },
    { name := phrase!"specific orbital energy of an orbit with semi-major axis $v$ for the gravitational parameter $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ m => pos m], doc := "`-μ/(2a)`",
      value := close <| lamT .real pos fun a => lamT .real pos fun m => neg (div m (mul (num 2) a)) },
    hohmann phrase!"first burn of the Hohmann transfer from radius $v$ to radius $v$ for the gravitational parameter $v$"
      (fun a b m => mul (sqrt (div m a)) (sub (sqrt (div (mul (num 2) b) (add a b))) (num 1))) "`√(μ/r₁)(√(2r₂/(r₁+r₂)) - 1)`",
    hohmann phrase!"second burn of the Hohmann transfer from radius $v$ to radius $v$ for the gravitational parameter $v$"
      (fun a b m => mul (sqrt (div m b)) (sub (num 1) (sqrt (div (mul (num 2) a) (add a b))))) "`√(μ/r₂)(1 - √(2r₁/(r₁+r₂)))`",
    { name := phrase!"synodic period of the periods $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun a b => and (pos b) (ne a b)], doc := "`1/|1/T₁ - 1/T₂|`",
      value := close <| lamT .real pos fun a => lamT .real (fun b => and (pos b) (ne a b)) fun b =>
        div (num 1) (abs (sub (div (num 1) a) (div (num 1) b))) },
    { name := phrase!"Hill radius of a body of mass $v$ orbiting a mass $v$ at distance $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ m => pos m, dom3 .real fun _ _ a => pos a], doc := "`a(m/(3M))^{1/3}`",
      value := close <| lamT .real pos fun m => lamT .real pos fun mm => lamT .real pos fun a => mul a (cbrt (div m (mul (num 3) mm))) }]

end Leanify.Orbits
