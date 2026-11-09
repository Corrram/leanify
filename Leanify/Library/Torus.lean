import Leanify.Library.Build

/-! # Vocabulary: functions on the torus `𝕋² = ℝ²/ℤ²`

A function on `𝕋²` is a real function of two real variables (curried,
`ℝ → ℝ → ℝ`) that is 1-periodic in each. The field has four constants, interpreted
in Mathlib by `Leanify.Torus.model` (`Leanify/Library/TorusModel.lean`):

* `smooth function $F$ on $\mathbb{T}^2$`: `ContDiff ℝ ⊤ (Function.uncurry F)` and
  1-periodic in each variable;
* `with zero mean`: `∫ x in 0..1, ∫ y in 0..1, F x y = 0` (the Haar mean);
* `the $C^m$ norm of $F$`: the largest supremum norm of the derivatives
  (`iteratedFDeriv`) of order at most `m` (for a nonnegative integer `m`);
* `the derivative of $F$ in the direction $(a,b)$`: `(x, y) ↦ DF(x, y)(a, b)`
  (`fderiv`).

An article fixes its notation itself, for example `We write $\|F\|_{C^m}$ for the
$C^m$ norm of $F$.` and `We write $NF$ for the derivative of $F$ in the direction
$(\sqrt2-1,1)$.` -/

namespace Leanify.Torus
open Build

/-- Functions of two real variables. -/
abbrev F2 : Ty := .real ⟶ .real ⟶ .real

def smooth : Nat := 0
def zeroMean : Nat := 1
def cNorm : Nat := 2
def dirDeriv : Nat := 3

def smoothNoun (sing plural : Phrase) : Noun :=
  { sing, plural, ty := F2, pred := .const smooth,
    doc := "`ContDiff ℝ ⊤ (Function.uncurry F)`, 1-periodic in each variable" }

def vocab : Vocab where
  consts := [F2 ⟶ .prop, F2 ⟶ .prop, .real ⟶ F2 ⟶ .real, F2 ⟶ .real ⟶ .real ⟶ F2]
  constNames := [w!"\\operatorname{Smooth}_{\\mathbb{T}^2}", w!"\\operatorname{ZeroMean}",
    w!"\\operatorname{C-norm}", w!"\\operatorname{D}"]
  constLean := [w!"Leanify.Torus.smoothT2", w!"Leanify.Torus.zeroMeanT2", w!"Leanify.Torus.cNormT2",
    w!"Leanify.Torus.dirDerivT2"]
  modules := [w!"Leanify.Library.TorusModel"]
  nouns := [
    smoothNoun phrase!"smooth function $v$ on $\\mathbb{T}^2$" phrase!"smooth functions $v$ on $\\mathbb{T}^2$",
    smoothNoun phrase!"smooth periodic function $v$ on $\\mathbb{R}^2$"
      phrase!"smooth periodic functions $v$ on $\\mathbb{R}^2$"]
  mods := [
    { phrase := phrase!"with zero mean", prenominal := false, ty := F2, pred := .const zeroMean,
      doc := "`∫ x in 0..1, ∫ y in 0..1, F x y = 0`" },
    { phrase := phrase!"of zero mean", prenominal := false, ty := F2, pred := .const zeroMean,
      doc := "`∫ x in 0..1, ∫ y in 0..1, F x y = 0`" },
    { phrase := phrase!"of zero Haar mean", prenominal := false, ty := F2, pred := .const zeroMean,
      doc := "`∫ x in 0..1, ∫ y in 0..1, F x y = 0`" },
    { phrase := phrase!"with mean zero", prenominal := false, ty := F2, pred := .const zeroMean,
      doc := "`∫ x in 0..1, ∫ y in 0..1, F x y = 0`" }]
  notions := [
    { name := phrase!"$C^v$ norm of $v$", value := .const cNorm, ty := .real ⟶ F2 ⟶ .real,
      doms := [some (predR fun m => and (isInt m) (le (num 0) m)), none],
      doc := "`⨆ k ≤ m, ⨆ p, ‖iteratedFDeriv ℝ k (Function.uncurry F) p‖` (`m` a nonnegative integer)" },
    { name := phrase!"derivative of $v$ in the direction $(v,v)$", value := .const dirDeriv,
      ty := F2 ⟶ .real ⟶ .real ⟶ F2,
      doc := "`fun x y => fderiv ℝ (Function.uncurry F) (x, y) (a, b)`" }]

end Leanify.Torus
