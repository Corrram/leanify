import Leanify.Library.Core

/-! # Vocabulary: acoustics

Sound speeds, levels and resonances, with the constants as arguments (`We write $c(g,R,T,M)$ for the speed of sound in an ideal gas with adiabatic index $g$, gas
constant $R$, temperature $T$ and molar mass $M$.`). Doppler shifts and string harmonics are in
the field `waves`.

* notions: the speed of sound `√(γRT/M)` in an ideal gas; the sound intensity level
  `10 log₁₀(I/I₀)` and the sound pressure level `20 log₁₀(p/p₀)`; the intensity `P/(4πr²)` of a
  point source; the resonant frequencies `nc/(2L)` of a pipe open at both ends and
  `(2n-1)c/(4L)` of a pipe closed at one end; the Sabine reverberation time `0.161 V/A`.

Every meaning is a term of the core language. -/

namespace Leanify.Acoustics
open Build Core

def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def log10 (x : B) : B := div (app (prim (.realFn .log)) x) (app (prim (.realFn .log)) (num 10))
def pi : B := prim .pi
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }
def pipe (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real posInt, dom2 .real fun _ l => pos l, dom3 .real fun _ _ c => pos c], doc,
    value := close <| lamT .real posInt fun n => lamT .real pos fun l => lamT .real pos fun c => body n l c }

def vocab : Vocab where
  notions := [
    { name := phrase!"speed of sound in an ideal gas with adiabatic index $v$, gas constant $v$, temperature $v$ and molar mass $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ r => pos r, dom3 .real fun _ _ t => pos t, dom4 .real fun _ _ _ m => pos m],
      doc := "`√(γRT/M)`",
      value := close <| lamT .real pos fun g => lamT .real pos fun r => lamT .real pos fun t => lamT .real pos fun m =>
        sqrt (div (mul g (mul r t)) m) },
    two phrase!"sound intensity level of the intensity $v$ for the reference intensity $v$" (fun i i0 => mul (num 10) (log10 (div i i0)))
      "`10 log₁₀(I/I₀)` in decibels",
    two phrase!"sound pressure level of the pressure $v$ for the reference pressure $v$" (fun p p0 => mul (num 20) (log10 (div p p0)))
      "`20 log₁₀(p/p₀)` in decibels",
    two phrase!"intensity at distance $v$ from a point source of power $v$" (fun r p => div p (mul (mul (num 4) pi) (mul r r)))
      "`P/(4πr²)`",
    pipe phrase!"frequency of the $v$th resonance of a pipe of length $v$ open at both ends with sound speed $v$"
      (fun n l c => div (mul n c) (mul (num 2) l)) "`nc/(2L)`",
    pipe phrase!"frequency of the $v$th resonance of a pipe of length $v$ closed at one end with sound speed $v$"
      (fun n l c => div (mul (sub (mul (num 2) n) (num 1)) c) (mul (num 4) l)) "`(2n-1)c/(4L)`",
    two phrase!"Sabine reverberation time of a room of volume $v$ with absorption area $v$"
      (fun v a => div (mul (div (num 161) (num 1000)) v) a) "`0.161 V/A` (in seconds, for metres)"]

end Leanify.Acoustics
