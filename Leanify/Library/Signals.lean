import Leanify.Library.Core

/-! # Vocabulary: signals and filters

The standard pulses of signal processing as real functions, and the closed-form quantities of
sampling and first-order filters (`We write $\Pi$ for the rectangular function.`). The
unnormalized sinc function is in the field `special`, channel capacities in `channels`.

* notions: the normalized sinc function `sin(πx)/(πx)` (`1` at `0`), the rectangular function
  (`1` on `|x| < 1/2`, `1/2` at `|x| = 1/2`), the triangular function `max(1 - |x|, 0)`, the unit
  step function (`1` for `x ≥ 0`, `0` otherwise) and the Gaussian pulse `e^{-x²/(2σ²)}`; the
  Nyquist rate `2B` of a bandwidth `B`; the signal-to-noise ratio `10 log₁₀(S/N)` in decibels;
  the cutoff frequency `1/(2πRC)` of an RC filter and the gain `1/√(1 + (f/f_c)²)` of a
  first-order low-pass filter.

Every meaning is a term of the core language. -/

namespace Leanify.Signals
open Build Core

abbrev F : Ty := Ty.rfun

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def sin (x : B) : B := app (prim (.realFn .sin)) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def pi : B := prim .pi
def half : B := div (num 1) (num 2)

def vocab : Vocab where
  notions := [
    { name := phrase!"normalized sinc function", ty := F, doc := "`x ↦ sin(πx)/(πx)`, and `1` at `0`",
      value := close <| lamR fun x => cases (eq x (num 0)) (num 1) (div (sin (mul pi x)) (mul pi x)) },
    { name := phrase!"rectangular function", ty := F, doc := "`1` on `|x| < 1/2`, `1/2` at `|x| = 1/2`, `0` elsewhere",
      value := close <| lamR fun x => cases (lt (abs x) half) (num 1) (cases (eq (abs x) half) half (num 0)) },
    { name := phrase!"triangular function", ty := F, doc := "`x ↦ max(1 - |x|, 0)`",
      value := close <| lamR fun x => app2 (prim .max) (sub (num 1) (abs x)) (num 0) },
    { name := phrase!"unit step function", ty := F, doc := "`1` for `x ≥ 0`, `0` for `x < 0` (Heaviside, with value `1` at `0`)",
      value := close <| lamR fun x => cases (le (num 0) x) (num 1) (num 0) },
    { name := phrase!"Gaussian pulse of width $v$", ty := .real ⟶ F, doms := [dom1 .real pos],
      doc := "`x ↦ e^{-x²/(2σ²)}`",
      value := close <| lamT .real pos fun s => lamR fun x => exp (neg (div (mul x x) (mul (num 2) (mul s s)))) },
    { name := phrase!"Nyquist rate for the bandwidth $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`2B`: the sampling rate above which a signal of bandwidth `B` is determined by its samples",
      value := close <| lamT .real pos fun b => mul (num 2) b },
    { name := phrase!"signal-to-noise ratio in decibels for signal power $v$ and noise power $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ n => pos n], doc := "`10 log₁₀(S/N)`",
      value := close <| lamT .real pos fun s => lamT .real pos fun n => div (mul (num 10) (log (div s n))) (log (num 10)) },
    { name := phrase!"cutoff frequency of the RC filter with resistance $v$ and capacitance $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ c => pos c], doc := "`1/(2πRC)`",
      value := close <| lamT .real pos fun r => lamT .real pos fun c => div (num 1) (mul (mul (num 2) pi) (mul r c)) },
    { name := phrase!"gain of the first-order low-pass filter with cutoff frequency $v$ at frequency $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ f => le (num 0) f], doc := "`1/√(1 + (f/f_c)²)`",
      value := close <| lamT .real pos fun c => lamT .real (fun f => le (num 0) f) fun f =>
        div (num 1) (sqrt (add (num 1) (mul (div f c) (div f c)))) }]

end Leanify.Signals
