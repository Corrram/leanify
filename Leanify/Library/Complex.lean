import Leanify.Library.Build

/-! # Vocabulary: the complex numbers

A field that declares a type of its own, `ℂ`, and says what notation means on it, as
Python's classes do with `__add__`: every method below is a constant, interpreted in
Mathlib by `Leanify.Complex.model` (`Leanify/Library/ComplexModel.lean`).

* `\mathbb{C}` (as a domain, `z\in\mathbb{C}`) and `complex number`;
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
end Const
open Const in

def vocab : Vocab where
  types := [w!"\\mathbb{C}"]
  consts := [.real ⟶ C, C ⟶ C ⟶ C, C ⟶ C ⟶ C, C ⟶ C ⟶ C, C ⟶ C ⟶ C, C ⟶ C, C ⟶ .real ⟶ C,
    C ⟶ .real, C ⟶ C, C ⟶ .real, C ⟶ .real, C ⟶ C, C,
    .real ⟶ .real ⟶ (.real ⟶ C) ⟶ C, .real ⟶ .real ⟶ (.real ⟶ C) ⟶ C]
  constNames := [w!"", w!"+", w!"-", w!"\\cdot", w!"/", w!"-", w!"^", w!"\\lvert #\\rvert",
    w!"\\overline{#}", w!"\\operatorname{Re}(#)", w!"\\operatorname{Im}(#)", w!"\\exp(#)",
    w!"\\mathrm{i}", w!"\\sum", w!"\\prod"]
  nouns := [
    { sing := phrase!"complex number", plural := phrase!"complex numbers", ty := C,
      pred := close (lamT C (fun _ => tt) fun _ => tt), doc := "a complex number (Mathlib `ℂ`)" }]
  methods := [
    ⟨C, .ofReal, ofReal, "a real number `x` as the complex number `(x : ℂ)`"⟩,
    ⟨C, .add, add, "`z + w`"⟩, ⟨C, .sub, sub, "`z - w`"⟩, ⟨C, .mul, mul, "`z * w`"⟩,
    ⟨C, .div, div, "`z / w`, for `w ≠ 0`"⟩, ⟨C, .neg, neg, "`-z`"⟩,
    ⟨C, .pow, pow, "`z ^ n`, for a natural number `n`"⟩, ⟨C, .abs, abs, "the modulus `‖z‖`"⟩,
    ⟨C, .decor w!"\\overline", conj, "the conjugate `starRingEnd ℂ z`"⟩,
    ⟨C, .decor w!"\\bar", conj, "the conjugate `starRingEnd ℂ z`"⟩,
    ⟨C, .fn w!"\\Re", re, "the real part `z.re`"⟩, ⟨C, .fn w!"Re", re, "the real part `z.re`"⟩,
    ⟨C, .fn w!"\\Im", im, "the imaginary part `z.im`"⟩, ⟨C, .fn w!"Im", im, "the imaginary part `z.im`"⟩,
    ⟨C, .fn w!"\\exp", exp, "`Complex.exp z` (also `e^{z}`)"⟩,
    ⟨C, .sum, sum, "`∑ k ∈ Finset.Icc ⌈a⌉ ⌊b⌋, f k`"⟩, ⟨C, .prod, prod, "`∏ k ∈ Finset.Icc ⌈a⌉ ⌊b⌋, f k`"⟩]
  symbols := [
    { sym := w!"\\mathbb{C}", ty := C, doc := "the complex numbers (Mathlib `ℂ`), as a domain" },
    { sym := w!"\\mathrm{i}", ty := C, const := some I, doc := "the imaginary unit (Mathlib `Complex.I`)" }]

end Leanify.Complex
