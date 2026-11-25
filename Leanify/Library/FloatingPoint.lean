import Leanify.Library.Core

/-! # Vocabulary: floating-point arithmetic

The parameters of a floating-point system with base `b`, precision `p` and exponent range
`[e_min, e_max]` (significands `d₀.d₁…d_{p-1}`), and the errors of approximations (`We write
$u(b,p)$ for the unit roundoff for base $b$ and precision $p$.`).

* modifiers: `representable with $p$ digits in base $b$` (`0`, or `m b^e` with integers `m`,
  `e` and `|m| < b^p`).
* notions: the machine epsilon `b^{1-p}` and the unit roundoff `b^{1-p}/2`; the largest number
  `(1 - b^{-p}) b^{e_max + 1}`, the smallest positive normal number `b^{e_min}` and subnormal
  number `b^{e_min - p + 1}`; the number `2(b-1)b^{p-1}(e_max - e_min + 1)` of normal numbers;
  the absolute error `|x̂ - x|` and the relative error `|x̂ - x|/|x|` of an approximation `x̂`
  of `x`; the rounding `⌊10^d x + 1/2⌋/10^d` of `x` to `d` decimal places.

Every meaning is a term of the core language. -/

namespace Leanify.FloatingPoint
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def base (b : B) : B := and (isInt b) (le (num 2) b)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real base, dom2 .real fun _ p => posInt p], doc,
    value := close <| lamT .real base fun b => lamT .real posInt fun p => body b p }

def vocab : Vocab where
  mods := [
    { phrase := phrase!"representable with $v$ digits in base $v$", prenominal := false, ty := .real,
      pred := close <| lamT .real posInt fun p => lamT .real base fun b => lamR fun x =>
        or (eq x (num 0)) (exInt fun m => exInt fun e => and (lt (abs m) (zpow b p)) (eq x (mul m (zpow b e)))),
      doc := "`0`, or `m b^e` with integers `m`, `e` and `|m| < b^p`: a number with a `p`-digit significand in base `b`" }]
  notions := [
    two phrase!"machine epsilon for base $v$ and precision $v$" (fun b p => zpow b (sub (num 1) p))
      "`b^{1-p}`: the distance from `1` to the next floating-point number",
    two phrase!"unit roundoff for base $v$ and precision $v$" (fun b p => div (zpow b (sub (num 1) p)) (num 2))
      "`b^{1-p}/2`: the largest relative error of rounding to nearest",
    { name := phrase!"largest floating-point number for base $v$, precision $v$ and maximal exponent $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real base, dom2 .real fun _ p => posInt p, dom3 .real fun _ _ e => isInt e],
      doc := "`(1 - b^{-p}) b^{e_max + 1}`",
      value := close <| lamT .real base fun b => lamT .real posInt fun p => lamT .real isInt fun e =>
        mul (sub (num 1) (zpow b (neg p))) (zpow b (add e (num 1))) },
    { name := phrase!"smallest positive normal number for base $v$ and minimal exponent $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real base, dom2 .real fun _ e => isInt e], doc := "`b^{e_min}`",
      value := close <| lamT .real base fun b => lamT .real isInt fun e => zpow b e },
    { name := phrase!"smallest positive subnormal number for base $v$, precision $v$ and minimal exponent $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real base, dom2 .real fun _ p => posInt p, dom3 .real fun _ _ e => isInt e],
      doc := "`b^{e_min - p + 1}`",
      value := close <| lamT .real base fun b => lamT .real posInt fun p => lamT .real isInt fun e =>
        zpow b (add (sub e p) (num 1)) },
    { name := phrase!"number of normal floating-point numbers for base $v$, precision $v$ and exponents from $v$ to $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real base, dom2 .real fun _ p => posInt p, dom3 .real fun _ _ e => isInt e, dom4 .real fun _ _ e f => and (isInt f) (le e f)],
      doc := "`2(b-1)b^{p-1}(e_max - e_min + 1)`, with both signs",
      value := close <| lamT .real base fun b => lamT .real posInt fun p => lamT .real isInt fun e =>
        lamT .real (fun f => and (isInt f) (le e f)) fun f =>
          mul (mul (num 2) (mul (sub b (num 1)) (zpow b (sub p (num 1))))) (add (sub f e) (num 1)) },
    { name := phrase!"absolute error of $v$ as an approximation of $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`|x̂ - x|`", value := close <| lamR fun a => lamR fun x => abs (sub a x) },
    { name := phrase!"relative error of $v$ as an approximation of $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ x => ne x (num 0)],
      doc := "`|x̂ - x|/|x|`, for `x ≠ 0`",
      value := close <| lamR fun a => lamT .real (fun x => ne x (num 0)) fun x => div (abs (sub a x)) (abs x) },
    { name := phrase!"rounding of $v$ to $v$ decimal places", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ d => natP d],
      doc := "`⌊10^d x + 1/2⌋/10^d`: to the nearest multiple of `10^{-d}`, halves up",
      value := close <| lamR fun x => lamT .real natP fun d =>
        div (floor (add (mul (zpow (num 10) d) x) (div (num 1) (num 2)))) (zpow (num 10) d) }]

end Leanify.FloatingPoint
