import Leanify.Library.Core

/-! # Vocabulary: classical mechanics

The closed-form quantities of elementary mechanics, by their parameters, with the constants of
nature as arguments (`We write $R(u,a,g)$ for the range of a projectile with speed $u$ and
angle $a$ under gravity $g$.`).

* notions: the range `u² sin(2a)/g`, the maximal height `u² sin²a/(2g)` and the time of flight
  `2u sin a/g` of a projectile launched from level ground with speed `u` at angle `a`; the
  period `2π√(ℓ/g)` of a pendulum of length `ℓ` (small oscillations); the natural frequency
  `√(k/m)`, the period `2π√(m/k)` and the damping ratio `c/(2√(mk))` of the oscillator
  `m x'' + c x' + k x = 0`; the kinetic energy `mv²/2`; the circular orbital speed `√(μ/r)`, the
  escape velocity `√(2μ/r)` at distance `r` and the orbital period `2π√(a³/μ)` of an orbit with
  semi-major axis `a` (Kepler's third law), for the gravitational parameter `μ = GM`.

Every meaning is a term of the core language. -/

namespace Leanify.Mechanics
open Build Core

def pos (x : B) : B := lt (num 0) x
def rpow (x s : B) : B := app2 (prim .rpow) x s
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def sin (x : B) : B := app (prim (.realFn .sin)) x
def pi : B := prim .pi
def angle (a : B) : B := and (lt (num 0) a) (lt a (div pi (num 2)))
def twoPos (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }
def projectile (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ a => angle a, dom3 .real fun _ _ g => pos g], doc,
    value := close <| lamT .real pos fun u => lamT .real angle fun a => lamT .real pos fun g => body u a g }

def vocab : Vocab where
  notions := [
    projectile phrase!"range of a projectile with speed $v$ and angle $v$ under gravity $v$"
      (fun u a g => div (mul (mul u u) (sin (mul (num 2) a))) g) "`u² sin(2a)/g`, on level ground, for `0 < a < π/2`",
    projectile phrase!"maximal height of a projectile with speed $v$ and angle $v$ under gravity $v$"
      (fun u a g => div (mul (mul u u) (mul (sin a) (sin a))) (mul (num 2) g)) "`u² sin²a/(2g)`",
    projectile phrase!"time of flight of a projectile with speed $v$ and angle $v$ under gravity $v$"
      (fun u a g => div (mul (num 2) (mul u (sin a))) g) "`2u sin a/g`, on level ground",
    twoPos phrase!"period of a pendulum of length $v$ under gravity $v$"
      (fun l g => mul (mul (num 2) pi) (sqrt (div l g))) "`2π√(ℓ/g)`, for small oscillations",
    twoPos phrase!"natural frequency of the oscillator with mass $v$ and spring constant $v$"
      (fun m k => sqrt (div k m)) "`√(k/m)`, the angular frequency of `m x'' + k x = 0`",
    twoPos phrase!"period of the oscillator with mass $v$ and spring constant $v$"
      (fun m k => mul (mul (num 2) pi) (sqrt (div m k))) "`2π√(m/k)`",
    { name := phrase!"damping ratio of the oscillator with mass $v$, damping $v$ and spring constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ c => le (num 0) c, dom3 .real fun _ _ k => pos k],
      doc := "`c/(2√(mk))` for `m x'' + c x' + k x = 0`: underdamped below `1`, critically damped at `1`, overdamped above",
      value := close <| lamT .real pos fun m => lamT .real (fun c => le (num 0) c) fun c => lamT .real pos fun k =>
        div c (mul (num 2) (sqrt (mul m k))) },
    { name := phrase!"kinetic energy of a body of mass $v$ with speed $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none], doc := "`mv²/2`",
      value := close <| lamT .real pos fun m => lamR fun v => div (mul m (mul v v)) (num 2) },
    twoPos phrase!"circular orbital speed at distance $v$ for the gravitational parameter $v$"
      (fun r μ => sqrt (div μ r)) "`√(μ/r)`, with `μ = GM`",
    twoPos phrase!"escape velocity at distance $v$ for the gravitational parameter $v$"
      (fun r μ => sqrt (div (mul (num 2) μ) r)) "`√(2μ/r)`, with `μ = GM`",
    twoPos phrase!"orbital period for the semi-major axis $v$ and the gravitational parameter $v$"
      (fun a μ => mul (mul (num 2) pi) (sqrt (div (mul a (mul a a)) μ))) "`2π√(a³/μ)` (Kepler's third law), with `μ = GM`"]

end Leanify.Mechanics
