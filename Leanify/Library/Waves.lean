import Leanify.Library.Core

/-! # Vocabulary: waves and optics

The closed-form quantities of waves, sound and geometric optics, by their parameters (`We write
$\theta_t(a,n_1,n_2)$ for the angle of refraction for the angle of incidence $a$ and the
refractive indices $n_1$ and $n_2$.`).

* notions: the wavelength `c/f`; the frequency `f (c + u)/(c - w)` heard by an observer moving
  towards the source at speed `u` from a source moving towards the observer at speed `w`
  (Doppler); the beat frequency `|f₁ - f₂|`; the frequency `nc/(2L)` of the `n`th harmonic of a
  string of length `L`, and the wave speed `√(T/μ)` on a string with tension `T` and linear
  density `μ`; the angle of refraction (`n₁ sin a = n₂ sin t`, Snell's law), the critical angle
  `arcsin(n₂/n₁)` and the Brewster angle `arctan(n₂/n₁)`, as angles in `[0, π/2]`; the level
  `10 log₁₀ r` in decibels of a power ratio `r`; the focal length `1/(1/d_o + 1/d_i)` of a thin
  lens with object and image distances `d_o`, `d_i`.

Every meaning is a term of the core language. -/

namespace Leanify.Waves
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def sin (x : B) : B := app (prim (.realFn .sin)) x
def tan (x : B) : B := app (prim (.realFn .tan)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def pi : B := prim .pi
def angle (t : B) : B := and (le (num 0) t) (le t (div pi (num 2)))
def twoPos (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }

def vocab : Vocab where
  notions := [
    twoPos phrase!"wavelength for wave speed $v$ and frequency $v$" (fun c f => div c f) "`c/f`",
    { name := phrase!"Doppler frequency for source frequency $v$, wave speed $v$, observer speed $v$ and source speed $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ c => pos c, dom3 .real fun _ c u => lt (neg c) u, dom4 .real fun _ c _ w => lt w c],
      doc := "`f (c + u)/(c - w)`: observer and source moving towards each other at speeds `u` and `w`",
      value := close <| lamT .real pos fun f => lamT .real pos fun c => lamT .real (fun u => lt (neg c) u) fun u =>
        lamT .real (fun w => lt w c) fun w => div (mul f (add c u)) (sub c w) },
    { name := phrase!"beat frequency of $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ g => pos g], doc := "`|f₁ - f₂|`",
      value := close <| lamT .real pos fun f => lamT .real pos fun g => abs (sub f g) },
    { name := phrase!"frequency of the $v$th harmonic of a string of length $v$ with wave speed $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => and (isInt n) (le (num 1) n), dom2 .real fun _ l => pos l, dom3 .real fun _ _ c => pos c],
      doc := "`nc/(2L)`, with both ends fixed",
      value := close <| lamT .real (fun n => and (isInt n) (le (num 1) n)) fun n => lamT .real pos fun l => lamT .real pos fun c =>
        div (mul n c) (mul (num 2) l) },
    twoPos phrase!"wave speed on a string with tension $v$ and linear density $v$" (fun t m => sqrt (div t m)) "`√(T/μ)`",
    { name := phrase!"angle of refraction for the angle of incidence $v$ and the refractive indices $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real angle, dom2 .real fun _ n => pos n, dom3 .real fun a n m => and (pos m) (le (mul n (sin a)) m)],
      doc := "the `t ∈ [0, π/2]` with `n₁ sin a = n₂ sin t` (Snell's law), short of total internal reflection",
      value := close <| lamT .real angle fun a => lamT .real pos fun n => lamT .real (fun m => and (pos m) (le (mul n (sin a)) m)) fun m =>
        theR fun t => and (angle t) (eq (mul m (sin t)) (mul n (sin a))) },
    { name := phrase!"critical angle for the refractive indices $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun n m => and (pos m) (lt m n)],
      doc := "`arcsin(n₂/n₁)`, for `n₂ < n₁`: the `t ∈ [0, π/2]` with `sin t = n₂/n₁`",
      value := close <| lamT .real pos fun n => lamT .real (fun m => and (pos m) (lt m n)) fun m =>
        theR fun t => and (angle t) (eq (sin t) (div m n)) },
    { name := phrase!"Brewster angle for the refractive indices $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ m => pos m],
      doc := "`arctan(n₂/n₁)`: the `t ∈ (0, π/2)` with `tan t = n₂/n₁`",
      value := close <| lamT .real pos fun n => lamT .real pos fun m =>
        theR fun t => and (and (lt (num 0) t) (lt t (div pi (num 2)))) (eq (tan t) (div m n)) },
    { name := phrase!"level in decibels of the power ratio $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`10 log₁₀ r`", value := close <| lamT .real pos fun r => div (mul (num 10) (log r)) (log (num 10)) },
    twoPos phrase!"focal length of a thin lens with object distance $v$ and image distance $v$"
      (fun o i => div (num 1) (add (div (num 1) o) (div (num 1) i))) "`1/(1/d_o + 1/d_i)` (thin lens equation)"]

end Leanify.Waves
