import Leanify.Library.Core

/-! # Vocabulary: kinematics and collisions

Uniformly accelerated motion, circular motion and one-dimensional collisions, by their
parameters (`We write $s(t,u,a)$ for the displacement after time $t$ with initial velocity $u$
and acceleration $a$.`). Projectiles, oscillators and orbits are in the field `mechanics`.

* notions: the displacement `ut + at²/2` and the velocity `u + at` after time `t` at constant
  acceleration; the stopping distance `u²/(2a)` from speed `u` at deceleration `a`; the
  centripetal acceleration `v²/r` and the period `2πr/v` of uniform circular motion; the
  velocities `((m₁ - m₂)u₁ + 2m₂u₂)/(m₁ + m₂)` and `((m₂ - m₁)u₂ + 2m₁u₁)/(m₁ + m₂)` after an
  elastic collision, and the common velocity `(m₁u₁ + m₂u₂)/(m₁ + m₂)` after a perfectly
  inelastic one; the kinetic energy lost in a perfectly inelastic collision,
  `m₁m₂(u₁ - u₂)²/(2(m₁ + m₂))`.

Every meaning is a term of the core language. -/

namespace Leanify.Kinematics
open Build Core

def pos (x : B) : B := lt (num 0) x
def pi : B := prim .pi
def collision (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ m => pos m, none, none], doc,
    value := close <| lamT .real pos fun m1 => lamT .real pos fun m2 => lamR fun u1 => lamR fun u2 => body m1 m2 u1 u2 }

def vocab : Vocab where
  notions := [
    { name := phrase!"displacement after time $v$ with initial velocity $v$ and acceleration $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, none, none], doc := "`ut + at²/2`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamR fun u => lamR fun a => add (mul u t) (div (mul a (mul t t)) (num 2)) },
    { name := phrase!"velocity after time $v$ with initial velocity $v$ and acceleration $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, none, none], doc := "`u + at`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamR fun u => lamR fun a => add u (mul a t) },
    { name := phrase!"stopping distance from speed $v$ at deceleration $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun u => le (num 0) u, dom2 .real fun _ a => pos a], doc := "`u²/(2a)`",
      value := close <| lamT .real (fun u => le (num 0) u) fun u => lamT .real pos fun a => div (mul u u) (mul (num 2) a) },
    { name := phrase!"centripetal acceleration at speed $v$ on a circle of radius $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ r => pos r], doc := "`v²/r`",
      value := close <| lamR fun v => lamT .real pos fun r => div (mul v v) r },
    { name := phrase!"period of uniform circular motion at speed $v$ on a circle of radius $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ r => pos r], doc := "`2πr/v`",
      value := close <| lamT .real pos fun v => lamT .real pos fun r => div (mul (mul (num 2) pi) r) v },
    collision phrase!"velocity of the first body after an elastic collision of masses $v$ and $v$ with velocities $v$ and $v$"
      (fun m1 m2 u1 u2 => div (add (mul (sub m1 m2) u1) (mul (mul (num 2) m2) u2)) (add m1 m2))
      "`((m₁ - m₂)u₁ + 2m₂u₂)/(m₁ + m₂)`",
    collision phrase!"velocity of the second body after an elastic collision of masses $v$ and $v$ with velocities $v$ and $v$"
      (fun m1 m2 u1 u2 => div (add (mul (sub m2 m1) u2) (mul (mul (num 2) m1) u1)) (add m1 m2))
      "`((m₂ - m₁)u₂ + 2m₁u₁)/(m₁ + m₂)`",
    collision phrase!"velocity after a perfectly inelastic collision of masses $v$ and $v$ with velocities $v$ and $v$"
      (fun m1 m2 u1 u2 => div (add (mul m1 u1) (mul m2 u2)) (add m1 m2)) "`(m₁u₁ + m₂u₂)/(m₁ + m₂)`",
    collision phrase!"kinetic energy lost in a perfectly inelastic collision of masses $v$ and $v$ with velocities $v$ and $v$"
      (fun m1 m2 u1 u2 => div (mul (mul m1 m2) (mul (sub u1 u2) (sub u1 u2))) (mul (num 2) (add m1 m2))) "`m₁m₂(u₁ - u₂)²/(2(m₁ + m₂))`"]

end Leanify.Kinematics
