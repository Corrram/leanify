import Leanify.Library.Core

/-! # Vocabulary: special functions and constants

The gamma and beta functions, the Riemann zeta function on `(1, ∞)`, the Bernoulli numbers,
the sinc function, the Euler–Mascheroni constant and the golden ratio. `\Gamma(x)` and
`\zeta(s)` are symbols of the field (an article that names it does not use these letters for
anything else); the others are notions (`We write $B(x,y)$ for the beta function of $x$ and
$y$.`).

The functions have domains: `\Gamma` is defined except at `0, -1, -2, …`, the beta function
for positive arguments, `\zeta` for `s > 1` (Mathlib's `riemannZeta` has values elsewhere, by
analytic continuation; an article that uses them has to say so). The Lean meanings are
Mathlib's (`Real.Gamma`, `bernoulli`, `Real.sinc`, `Real.eulerMascheroniConstant`) or written
in `Leanify/Library/SpecialModel.lean`. -/

namespace Leanify.Special
open Build Core

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def gamma : Nat := 0
def beta : Nat := 1
def zeta : Nat := 2
def bernoulli : Nat := 3
def sinc : Nat := 4
def eulerGamma : Nat := 5
end Const
open Const

/-- Not `0, -1, -2, …`. -/
def gammaDom : Tm := predR fun x => not (and (isInt x) (le x (num 0)))
def posDom : Tm := predR fun x => lt (num 0) x
def zetaDom : Tm := predR fun s => lt (num 1) s

/-- `(1 + √5)/2`. -/
def golden : Tm := close <| div (add (num 1) (app2 (prim .rpow) (num 5) (div (num 1) (num 2)))) (num 2)

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real]
  constNames := [w!"\\Gamma", w!"\\mathrm{B}", w!"\\zeta", w!"B_{#}", w!"\\operatorname{sinc}", w!"\\gamma"]
  constLean := [w!"Real.Gamma", w!"Leanify.Special.beta", w!"Leanify.Special.zeta", w!"Leanify.Special.bernoulli",
    w!"Real.sinc", w!"Real.eulerMascheroniConstant"]
  modules := [w!"Leanify.Library.SpecialModel"]
  symbols := [
    { sym := w!"\\Gamma", ty := Ty.rfun, const := some gamma, doms := [some gammaDom],
      doc := "the gamma function, except at `0, -1, -2, …` (Mathlib `Real.Gamma`)" },
    { sym := w!"\\zeta", ty := Ty.rfun, const := some zeta, doms := [some zetaDom],
      doc := "the Riemann zeta function `∑ n^{-s}`, for `s > 1` (Mathlib `riemannZeta`)" }]
  notions := [
    { name := phrase!"gamma function", value := close (lamT .real (fun x => app (lift gammaDom) x) fun x =>
        app (const gamma) x), ty := Ty.rfun, doc := "`Γ(x) = ∫_0^∞ t^{x-1} e^{-t} dt`, extended (Mathlib `Real.Gamma`)" },
    { name := phrase!"beta function of $v$ and $v$", value := .const beta, ty := .real ⟶ .real ⟶ .real,
      doms := [some posDom, some posDom], doc := "`B(x,y) = Γ(x)Γ(y)/Γ(x+y)`, for `x, y > 0`" },
    { name := phrase!"Riemann zeta function", value := close (lamT .real (fun s => app (lift zetaDom) s) fun s =>
        app (const zeta) s), ty := Ty.rfun, doc := "`ζ(s) = ∑_{n ≥ 1} n^{-s}`, for `s > 1`" },
    { name := phrase!"$v$th Bernoulli number", value := .const bernoulli, ty := .real ⟶ .real,
      doms := [some nonnegInt], doc := "`B_0 = 1`, `B_1 = -1/2`, `B_2 = 1/6`, … (Mathlib `bernoulli`)" },
    { name := phrase!"sinc function", value := .const sinc, ty := Ty.rfun,
      doc := "`sin x / x`, and `1` at `0` (Mathlib `Real.sinc`)" },
    { name := phrase!"Euler-Mascheroni constant", value := .const eulerGamma, ty := .real,
      doc := "`γ = lim (H_n - log n)` (Mathlib `Real.eulerMascheroniConstant`)" },
    { name := phrase!"Euler's constant", value := .const eulerGamma, ty := .real,
      doc := "`γ = lim (H_n - log n)` (Mathlib `Real.eulerMascheroniConstant`)" },
    { name := phrase!"golden ratio", value := golden, ty := .real, doc := "`(1 + √5)/2` (Mathlib `goldenRatio`)" }]

end Leanify.Special
