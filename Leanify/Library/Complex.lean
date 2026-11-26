import Leanify.Library.Build

/-! # Vocabulary: the complex numbers

A field that declares a type of its own, `ℂ`, and says what notation means on it, as
Python's classes do with `__add__`: every method below is a constant, interpreted in
Mathlib by `Leanify.Complex.model` (`Leanify/Library/ComplexModel.lean`).

* `\mathbb{C}` (as a domain, `z\in\mathbb{C}`) and `complex number`;
* functions of a complex variable: `entire function`, `holomorphic` (on the domain of the
  signature `f\colon U\to\mathbb{C}`, or `on $U$`), `bounded`, `constant`, `nonconstant`; sets
  of complex numbers: `subset of $\mathbb{C}$`, `open`, `connected`, `domain in $\mathbb{C}$`;
* `\mathrm{i}`, the imaginary unit;
* a real number where a complex number is expected (`1+z`): `(x : ℂ)`;
* `z+w`, `z-w`, `zw`, `z/w` (defined for `w\ne0`), `-z`, `z^n` (for a natural number
  `n`), `|z|` (the modulus `‖z‖`), `\overline{z}` and `\bar z` (the conjugate),
  `\operatorname{Re}`, `\Re`, `\operatorname{Im}`, `\Im`, `\exp` and `e^{z}`
  (`Complex.exp`), and finite sums and products `\sum_{k=a}^{b}`, `\prod_{k=a}^{b}`.

There is no order on `ℂ`: `z\le w` is refused with a finding.

The names of the constants are how they are written (`Leanify/Render.lean`): an
operator, `#` for the argument, or nothing for a real number taken as a complex one. -/

namespace Leanify.Complex
open Build

/-- The complex numbers: the field's base type. -/
abbrev C : Ty := .base 0

/-! The indices of the constants (in their own namespace, apart from Mathlib's
`Complex.I`, `Complex.exp`, …). -/
namespace Const
def ofReal : Nat := 0
def add : Nat := 1
def sub : Nat := 2
def mul : Nat := 3
def div : Nat := 4
def neg : Nat := 5
def pow : Nat := 6
def abs : Nat := 7
def conj : Nat := 8
def re : Nat := 9
def im : Nat := 10
def exp : Nat := 11
def I : Nat := 12
def sum : Nat := 13
def prod : Nat := 14
def entire : Nat := 15
def holomorphicOn : Nat := 16
def boundedOn : Nat := 17
def constantOn : Nat := 18
def openSet : Nat := 19
def connectedSet : Nat := 20
end Const
open Const in

def vocab : Vocab where
  types := [w!"\\mathbb{C}"]
  consts := [.real ⟶ C, C ⟶ C ⟶ C, C ⟶ C ⟶ C, C ⟶ C ⟶ C, C ⟶ C ⟶ C, C ⟶ C, C ⟶ .real ⟶ C,
    C ⟶ .real, C ⟶ C, C ⟶ .real, C ⟶ .real, C ⟶ C, C,
    .real ⟶ .real ⟶ (.real ⟶ C) ⟶ C, .real ⟶ .real ⟶ (.real ⟶ C) ⟶ C,
    (C ⟶ C) ⟶ .prop, (C ⟶ .prop) ⟶ (C ⟶ C) ⟶ .prop, (C ⟶ .prop) ⟶ (C ⟶ C) ⟶ .prop,
    (C ⟶ .prop) ⟶ (C ⟶ C) ⟶ .prop, (C ⟶ .prop) ⟶ .prop, (C ⟶ .prop) ⟶ .prop]
  constNames := [w!"", w!"+", w!"-", w!"\\cdot", w!"/", w!"-", w!"^", w!"\\lvert #\\rvert",
    w!"\\overline{#}", w!"\\operatorname{Re}(#)", w!"\\operatorname{Im}(#)", w!"\\exp(#)",
    w!"\\mathrm{i}", w!"\\sum", w!"\\prod", w!"\\operatorname{Entire}", w!"\\operatorname{Holomorphic}",
    w!"\\operatorname{Bounded}", w!"\\operatorname{Constant}", w!"\\operatorname{Open}", w!"\\operatorname{Connected}"]
  constLean := [w!"Leanify.Complex.Lean.ofReal", w!"Leanify.Complex.Lean.add", w!"Leanify.Complex.Lean.sub",
    w!"Leanify.Complex.Lean.mul", w!"Leanify.Complex.Lean.div", w!"Leanify.Complex.Lean.neg",
    w!"Leanify.Complex.powNat", w!"Leanify.Complex.Lean.abs", w!"Leanify.Complex.Lean.conj",
    w!"Leanify.Complex.Lean.re", w!"Leanify.Complex.Lean.im", w!"Complex.exp", w!"Complex.I",
    w!"Leanify.Complex.finSum", w!"Leanify.Complex.finProd", w!"Leanify.Complex.Entire",
    w!"Leanify.Complex.HolomorphicOn", w!"Leanify.Complex.BoundedOn", w!"Leanify.Complex.ConstantOn",
    w!"Leanify.Complex.OpenSet", w!"Leanify.Complex.ConnectedSet"]
  typeLean := [(w!"Complex", w!"Leanify.Complex.Lean.zero")]
  modules := [w!"Leanify.Library.ComplexModel"]
  nouns := [
    { sing := phrase!"complex number", plural := phrase!"complex numbers", ty := C,
      pred := close (lamT C (fun _ => tt) fun _ => tt), doc := "a complex number (Mathlib `ℂ`)" },
    { sing := phrase!"entire function", plural := phrase!"entire functions", ty := C ⟶ C, pred := .const entire,
      doc := "complex differentiable at every point (Mathlib `Differentiable ℂ`)" },
    { sing := phrase!"subset $v$ of $\\mathbb{C}$", plural := phrase!"subsets $v$ of $\\mathbb{C}$", ty := C ⟶ .prop,
      pred := close (lamT (C ⟶ .prop) (fun _ => tt) fun _ => tt), doc := "a set of complex numbers" },
    { sing := phrase!"set of complex numbers", plural := phrase!"sets of complex numbers", ty := C ⟶ .prop,
      pred := close (lamT (C ⟶ .prop) (fun _ => tt) fun _ => tt), doc := "(Mathlib `Set ℂ`)" },
    { sing := phrase!"domain in $\\mathbb{C}$", plural := phrase!"domains in $\\mathbb{C}$", ty := C ⟶ .prop,
      pred := close (lamT (C ⟶ .prop) (fun _ => tt) fun u => and (app (const openSet) u) (app (const connectedSet) u)),
      doc := "an open connected set of complex numbers" }]
  mods := [
    { phrase := phrase!"entire", prenominal := true, ty := C ⟶ C, pred := .const entire,
      doc := "complex differentiable at every point (Mathlib `Differentiable ℂ`)" },
    { phrase := phrase!"bounded", prenominal := true, ty := C ⟶ C,
      pred := close (lamT (C ⟶ C) (fun _ => tt) fun f => app2 (const boundedOn) (lamT C (fun _ => tt) fun _ => tt) f),
      doc := "`‖f(z)‖ ≤ M` for all `z`" },
    { phrase := phrase!"constant", prenominal := true, ty := C ⟶ C,
      pred := close (lamT (C ⟶ C) (fun _ => tt) fun f => app2 (const constantOn) (lamT C (fun _ => tt) fun _ => tt) f),
      doc := "`f(z) = f(w)` for all `z`, `w`" },
    { phrase := phrase!"nonconstant", prenominal := true, ty := C ⟶ C,
      pred := close (lamT (C ⟶ C) (fun _ => tt) fun f => not (app2 (const constantOn) (lamT C (fun _ => tt) fun _ => tt) f)),
      doc := "not constant" },
    { phrase := phrase!"holomorphic on $v$", prenominal := false, ty := C ⟶ C,
      pred := close (lamT (C ⟶ .prop) (fun _ => tt) fun u => lamT (C ⟶ C) (fun _ => tt) fun f => app2 (const holomorphicOn) u f),
      doc := "complex differentiable at the points of `U` (Mathlib `DifferentiableOn ℂ`)" },
    { phrase := phrase!"holomorphic", prenominal := true, ty := C ⟶ C, onDomain := true,
      pred := close (lamT (C ⟶ .prop) (fun _ => tt) fun u => lamT (C ⟶ C) (fun _ => tt) fun f => app2 (const holomorphicOn) u f),
      doc := "on the domain of the signature `f\\colon U\\to\\mathbb{C}` (Mathlib `DifferentiableOn ℂ`)" },
    { phrase := phrase!"open", prenominal := true, ty := C ⟶ .prop, pred := .const openSet, doc := "(Mathlib `IsOpen`)" },
    { phrase := phrase!"connected", prenominal := true, ty := C ⟶ .prop, pred := .const connectedSet,
      doc := "nonempty, and connected (Mathlib `IsConnected`)" }]
  adjectives := [
    { words := [w!"holomorphic"], ty := C ⟶ C, onDomain := true,
      pred := close (lamT (C ⟶ C) (fun _ => tt) fun f => lamT (C ⟶ .prop) (fun _ => tt) fun d => app2 (const holomorphicOn) d f),
      doc := "on the domain of its signature, or on the set after `on` (Mathlib `DifferentiableOn ℂ`)" },
    { words := [w!"bounded"], ty := C ⟶ C, onDomain := true,
      pred := close (lamT (C ⟶ C) (fun _ => tt) fun f => lamT (C ⟶ .prop) (fun _ => tt) fun d => app2 (const boundedOn) d f),
      doc := "`‖f(z)‖ ≤ M` on the domain" },
    { words := [w!"constant"], ty := C ⟶ C, onDomain := true,
      pred := close (lamT (C ⟶ C) (fun _ => tt) fun f => lamT (C ⟶ .prop) (fun _ => tt) fun d => app2 (const constantOn) d f),
      doc := "the same value at any two points of the domain" }]
  methods := [
    ⟨C, .ofReal, ofReal, "a real number `x` as the complex number `(x : ℂ)`", none⟩,
    ⟨C, .add, add, "`z + w`", none⟩, ⟨C, .sub, sub, "`z - w`", none⟩, ⟨C, .mul, mul, "`z * w`", none⟩,
    ⟨C, .div, div, "`z / w`, for `w ≠ 0`", none⟩, ⟨C, .neg, neg, "`-z`", none⟩,
    ⟨C, .pow, pow, "`z ^ n`, for a natural number `n`", none⟩, ⟨C, .abs, abs, "the modulus `‖z‖`", none⟩,
    ⟨C, .decor w!"\\overline", conj, "the conjugate `starRingEnd ℂ z`", none⟩,
    ⟨C, .decor w!"\\bar", conj, "the conjugate `starRingEnd ℂ z`", none⟩,
    ⟨C, .fn w!"\\Re", re, "the real part `z.re`", none⟩, ⟨C, .fn w!"Re", re, "the real part `z.re`", none⟩,
    ⟨C, .fn w!"\\Im", im, "the imaginary part `z.im`", none⟩, ⟨C, .fn w!"Im", im, "the imaginary part `z.im`", none⟩,
    ⟨C, .fn w!"\\exp", exp, "`Complex.exp z` (also `e^{z}`)", none⟩,
    ⟨C, .sum, sum, "`∑ k ∈ Finset.Icc ⌈a⌉ ⌊b⌋, f k`", none⟩, ⟨C, .prod, prod, "`∏ k ∈ Finset.Icc ⌈a⌉ ⌊b⌋, f k`", none⟩]
  symbols := [
    { sym := w!"\\mathbb{C}", ty := C, doc := "the complex numbers (Mathlib `ℂ`), as a domain" },
    { sym := w!"\\mathrm{i}", ty := C, const := some I, doc := "the imaginary unit (Mathlib `Complex.I`)" }]

end Leanify.Complex
