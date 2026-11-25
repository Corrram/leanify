import Leanify.Library.Core

/-! # Vocabulary: channels and coding theorems

Capacities and rates of the standard channels of information theory, in bits
(`We write $C(p)$ for the capacity of the binary symmetric channel with crossover
probability $p$.`).

* notions: the binary entropy `h(p) = -p log₂ p - (1-p) log₂(1-p)` in bits; the capacity of the
  binary symmetric channel `1 - h(p)`, of the binary erasure channel `1 - ε`, of the Z-channel
  `log₂(1 + (1-p) p^{p/(1-p)})`, of the additive white Gaussian noise channel with
  signal-to-noise ratio `s` (`½ log₂(1 + s)`) and of the band-limited Gaussian channel with
  bandwidth `W` (`W log₂(1 + s)`, Shannon–Hartley); the rate-distortion function of a Bernoulli
  source with parameter `p` at Hamming distortion `D` (`h(p) - h(D)` for `D < min(p, 1-p)`) and of
  a Gaussian source with variance `σ²` (`½ log₂(σ²/D)` for `D < σ²`).

Every meaning is a term of the core language; `0 log 0 = 0`. -/

namespace Leanify.Channels
open Build Core

def log2 (x : B) : B := div (app (prim (.realFn .log)) x) (app (prim (.realFn .log)) (num 2))
def xlog2 (x : B) : B := cases (eq x (num 0)) (num 0) (mul x (log2 x))
def h (p : B) : B := neg (add (xlog2 p) (xlog2 (sub (num 1) p)))
def rpow (x y : B) : B := app2 (prim .rpow) x y
def prob (p : B) : B := and (le (num 0) p) (le p (num 1))
def pos (x : B) : B := lt (num 0) x
def one (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real d], doc, value := close <| lamT .real d body }

def vocab : Vocab where
  notions := [
    one phrase!"binary entropy in bits of $v$" prob h "`-p log₂ p - (1-p) log₂(1-p)`",
    one phrase!"capacity of the binary symmetric channel with crossover probability $v$" prob (fun p => sub (num 1) (h p))
      "`1 - h(p)` bits per use",
    one phrase!"capacity of the binary erasure channel with erasure probability $v$" prob (fun e => sub (num 1) e)
      "`1 - ε` bits per use",
    one phrase!"capacity of the Z-channel with crossover probability $v$" (fun p => and (le (num 0) p) (lt p (num 1)))
      (fun p => log2 (add (num 1) (mul (sub (num 1) p) (rpow p (div p (sub (num 1) p))))))
      "`log₂(1 + (1-p) p^{p/(1-p)})`, `0 ≤ p < 1` (`0^0 = 1`)",
    one phrase!"capacity of the Gaussian channel with signal-to-noise ratio $v$" (fun s => le (num 0) s)
      (fun s => div (log2 (add (num 1) s)) (num 2)) "`½ log₂(1 + s)` bits per use",
    { name := phrase!"capacity of the band-limited Gaussian channel with bandwidth $v$ and signal-to-noise ratio $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real fun s => le (num 0) s],
      doc := "`W log₂(1 + s)` bits per second (Shannon–Hartley)",
      value := close <| lamT .real pos fun w => lamT .real (fun s => le (num 0) s) fun s => mul w (log2 (add (num 1) s)) },
    { name := phrase!"rate-distortion function of the Bernoulli source with parameter $v$ at distortion $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real prob, dom2 .real fun _ d => and (le (num 0) d) (le d (num 1))],
      doc := "`h(p) - h(D)` for `D < min(p, 1-p)`, and `0` otherwise",
      value := close <| lamT .real prob fun p => lamT .real (fun d => and (le (num 0) d) (le d (num 1))) fun d =>
        cases (lt d (app2 (prim .min) p (sub (num 1) p))) (sub (h p) (h d)) (num 0) },
    { name := phrase!"rate-distortion function of the Gaussian source with variance $v$ at distortion $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real pos],
      doc := "`½ log₂(σ²/D)` for `D < σ²`, and `0` otherwise",
      value := close <| lamT .real pos fun s => lamT .real pos fun d => cases (lt d s) (div (log2 (div s d)) (num 2)) (num 0) }]

end Leanify.Channels
