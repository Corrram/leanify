import Leanify.Library.Core

/-! # Vocabulary: mathematics of music

Pitches, intervals and tunings by frequency ratios (`We write $f(n)$ for the frequency of the
$n$th piano key.`).

* notions: the frequency `440 · 2^{(n-49)/12}` of the `n`th key of a standard piano; the
  frequency `f · 2^{k/12}` of `k` equal-tempered semitones above `f`; the interval `1200 log₂(g/f)`
  in cents; the Pythagorean comma `3¹²/2¹⁹` and the syntonic comma `81/80`; the frequency ratio
  `2^{k/n}` of `k` steps of the equal temperament with `n` steps per octave; the MIDI note number
  `69 + 12 log₂(f/440)`.

Every meaning is a term of the core language. -/

namespace Leanify.Music
open Build Core

def pos (x : B) : B := lt (num 0) x
def rpow (x s : B) : B := app2 (prim .rpow) x s
def log2 (x : B) : B := div (app (prim (.realFn .log)) x) (app (prim (.realFn .log)) (num 2))
def zpow (x k : B) : B := app2 (prim .zpow) x k

def vocab : Vocab where
  notions := [
    { name := phrase!"frequency of the $v$th piano key", ty := .real ⟶ .real,
      doms := [dom1 .real fun n => and (isInt n) (and (le (num 1) n) (le n (num 88)))],
      doc := "`440 · 2^{(n-49)/12}`: the 49th key is A4 at 440 Hz",
      value := close <| lamT .real (fun n => and (isInt n) (and (le (num 1) n) (le n (num 88)))) fun n =>
        mul (num 440) (rpow (num 2) (div (sub n (num 49)) (num 12))) },
    { name := phrase!"frequency of $v$ semitones above $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ f => pos f], doc := "`f · 2^{k/12}` (equal temperament)",
      value := close <| lamR fun k => lamT .real pos fun f => mul f (rpow (num 2) (div k (num 12))) },
    { name := phrase!"interval in cents from $v$ to $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ g => pos g], doc := "`1200 log₂(g/f)`",
      value := close <| lamT .real pos fun f => lamT .real pos fun g => mul (num 1200) (log2 (div g f)) },
    { name := phrase!"Pythagorean comma", ty := .real, doc := "`3¹²/2¹⁹`: twelve fifths over seven octaves",
      value := close <| div (zpow (num 3) (num 12)) (zpow (num 2) (num 19)) },
    { name := phrase!"syntonic comma", ty := .real, doc := "`81/80`", value := close <| div (num 81) (num 80) },
    { name := phrase!"ratio of $v$ steps of the equal temperament with $v$ steps per octave", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ n => and (isInt n) (le (num 1) n)], doc := "`2^{k/n}`",
      value := close <| lamR fun k => lamT .real (fun n => and (isInt n) (le (num 1) n)) fun n => rpow (num 2) (div k n) },
    { name := phrase!"MIDI note number of the frequency $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`69 + 12 log₂(f/440)`", value := close <| lamT .real pos fun f => add (num 69) (mul (num 12) (log2 (div f (num 440)))) }]

end Leanify.Music
