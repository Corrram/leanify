import Leanify.Library.Core

/-! # Vocabulary: binary codes

Binary words and the counting bounds of coding theory. A word of length `n` is read as
its letters `x_1, …, x_n`, the values of a real function at `1, …, n` (as the samples of
the field `samples`): `Let $x$ be a binary word of length $n$.`

* adjectives of functions: `binary word of length $n$` (`x_i ∈ {0,1}` for `1 ≤ i ≤ n`);
* notions: the Hamming weight of the first `n` letters (`#{i ≤ n : x_i ≠ 0}`) and the
  Hamming distance between the first `n` letters of `x` and `y` (`#{i ≤ n : x_i ≠ y_i}`);
  the volume of the Hamming ball of radius `r` in dimension `n` (the number of binary words
  within distance `r` of one, a constant interpreted by `Leanify/Library/CodesModel.lean` with
  Mathlib's `hammingDist`; `∑_{i=0}^{r} \binom{n}{i}` is a theorem);
  for binary codes of length `n` and minimum distance `d`: the sphere-packing (Hamming)
  bound `⌊2^n/V(n,⌊(d-1)/2⌋)⌋`, the Singleton bound `2^{n-d+1}`, the Gilbert–Varshamov bound
  `⌈2^n/V(n,d-1)⌉`; the rate `log₂ M / n` of a code of length `n` with `M` codewords.

Every other meaning is a term of the core language; the bounds are the formulas they name. -/

namespace Leanify.Codes
open Build Core

abbrev F : Ty := Ty.rfun

def posInt (k : B) : B := and (isInt k) (le (num 1) k)
def natP (k : B) : B := and (isInt k) (le (num 0) k)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def ceil (x : B) : B := app (prim .ceil) x
def log (x : B) : B := app (prim (.realFn .log)) x
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def count (n : B) (p : B → B) : B := finSum (num 1) n fun i => cases (p i) (num 1) (num 0)
/-- The volume of the Hamming ball of radius `r` in dimension `n` (the constant `0`). -/
def ball (n r : B) : B := app2 (const 0) r n
def bounds (d n : B) : B := and (posInt d) (le d n)
def bound (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real posInt, dom2 .real bounds], doc,
    value := close <| lamT .real posInt fun n => lamT .real (fun d => bounds d n) fun d => body n d }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real]
  constNames := [w!"V(#2,#1)"]
  constLean := [w!"Leanify.Codes.hammingBall"]
  modules := [w!"Leanify.Library.CodesModel"]
  mods := [
    { phrase := phrase!"binary word of length $v$", prenominal := false, ty := F,
      pred := close <| lamR fun n => lamT F (fun _ => tt) fun x => and (natP n)
        (allR fun i => imp (and (isInt i) (and (le (num 1) i) (le i n))) (or (eq (app x i) (num 0)) (eq (app x i) (num 1)))),
      doc := "`x_i ∈ {0,1}` for `1 ≤ i ≤ n`" }]
  notions := [
    { name := phrase!"Hamming weight of the first $v$ terms of $v$", ty := .real ⟶ F ⟶ .real, doms := [dom1 .real natP, none],
      doc := "`#{1 ≤ i ≤ n : x_i ≠ 0}`",
      value := close <| lamT .real natP fun n => lamT F (fun _ => tt) fun x => count n fun i => ne (app x i) (num 0) },
    { name := phrase!"Hamming distance between the first $v$ terms of $v$ and $v$", ty := .real ⟶ F ⟶ F ⟶ .real,
      doms := [dom1 .real natP, none, none], doc := "`#{1 ≤ i ≤ n : x_i ≠ y_i}`",
      value := close <| lamT .real natP fun n => lamT F (fun _ => tt) fun x => lamT F (fun _ => tt) fun y =>
        count n fun i => ne (app x i) (app y i) },
    { name := phrase!"volume of the Hamming ball of radius $v$ in dimension $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real natP],
      doc := "the binary words of length `n` within Hamming distance `r` of one (Mathlib `hammingDist`; `∑_{i=0}^{r} \\binom{n}{i}`)",
      value := .const 0 },
    bound phrase!"sphere-packing bound for length $v$ and minimum distance $v$"
      (fun n d => floor (div (zpow (num 2) n) (ball n (floor (div (sub d (num 1)) (num 2))))))
      "`⌊2^n / V(n, ⌊(d-1)/2⌋)⌋` (Hamming bound): no binary code is larger",
    bound phrase!"Singleton bound for length $v$ and minimum distance $v$" (fun n d => zpow (num 2) (add (sub n d) (num 1)))
      "`2^{n-d+1}`: no binary code is larger",
    bound phrase!"Gilbert-Varshamov bound for length $v$ and minimum distance $v$"
      (fun n d => ceil (div (zpow (num 2) n) (ball n (sub d (num 1)))))
      "`⌈2^n / V(n, d-1)⌉`: some binary code is at least as large",
    { name := phrase!"rate of a code of length $v$ with $v$ codewords", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real posInt], doc := "`log₂ M / n`",
      value := close <| lamT .real posInt fun n => lamT .real posInt fun m => div (div (log m) (log (num 2))) n }]

end Leanify.Codes
