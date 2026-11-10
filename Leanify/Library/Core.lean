import Leanify.Library.Build

/-! # The core vocabulary

The words that every article may use, whatever its fields: real numbers and integers,
rational and irrational numbers, and the signs of a real number (`positive`,
`nonnegative`, `nonzero`). Leanify's numbers are real numbers; `x ∈ ℤ` is `isInt x`.
Every meaning is a term of the core language, so the core has no constants and no model.

*Natural number* has two meanings (with and without 0), so Leanify does not read it
alone: an article says *nonnegative integer* or *positive integer*, or states its
convention (`By a natural number we mean a nonnegative integer.`).

The words of one subject (primes, divisibility, copulas) are in the fields of
`Leanify.Library.Fields`. -/

namespace Leanify.Core
open Build

def integer : Tm := predR isInt
def nonnegInt : Tm := predR fun x => and (isInt x) (le (num 0) x)
def posInt : Tm := predR fun x => and (isInt x) (lt (num 0) x)
def negInt : Tm := predR fun x => and (isInt x) (lt x (num 0))
def rational : Tm := predR fun x => exInt fun p => exInt fun q => and (ne q (num 0)) (eq x (div p q))
def irrational : Tm := predR fun x => not (exInt fun p => exInt fun q => and (ne q (num 0)) (eq x (div p q)))
def nonzero : Tm := predR fun x => ne x (num 0)

/-- A noun of real numbers. -/
def noun (sing plural : Phrase) (pred : Tm) (doc : String) : Noun :=
  { sing, plural, ty := .real, pred, doc }

/-- An adjective of real numbers, before the noun. -/
def adj (p : Phrase) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := true, ty := .real, pred, doc }

/-- The words about numbers. -/
def numbers : Vocab where
  nouns := [
    noun phrase!"real number" phrase!"real numbers" (predR fun _ => tt) "a real number (`ℝ`)",
    noun phrase!"real" phrase!"reals" (predR fun _ => tt) "a real number (`ℝ`), as in `for every real $x$`",
    noun phrase!"integer" phrase!"integers" integer "an integer: `x ∈ ℤ` (Mathlib `Int`, as a real number)",
    noun phrase!"nonnegative integer" phrase!"nonnegative integers" nonnegInt "`x ∈ ℤ`, `0 ≤ x` (Mathlib `ℕ`)",
    noun phrase!"positive integer" phrase!"positive integers" posInt "`x ∈ ℤ`, `0 < x` (Mathlib `ℕ+`)",
    noun phrase!"negative integer" phrase!"negative integers" negInt "`x ∈ ℤ`, `x < 0`",
    { noun phrase!"natural number" phrase!"natural numbers" nonnegInt "with 0, as in Mathlib (`ℕ`)" with
      field := w!"core (with 0)" },
    { noun phrase!"natural number" phrase!"natural numbers" posInt "without 0 (`ℕ+`)" with
      field := w!"core (without 0)" },
    noun phrase!"rational number" phrase!"rational numbers" rational "`x ∈ ℚ` (Mathlib `Set.range ((↑) : ℚ → ℝ)`)",
    noun phrase!"irrational number" phrase!"irrational numbers" irrational "`x ∉ ℚ` (Mathlib `Irrational`)"]
  mods := [
    adj phrase!"rational" rational "`x ∈ ℚ`",
    adj phrase!"irrational" irrational "`x ∉ ℚ` (Mathlib `Irrational`)",
    adj phrase!"nonzero" nonzero "`x ≠ 0`",
    adj phrase!"positive" (predR fun x => lt (num 0) x) "`x > 0`",
    adj phrase!"negative" (predR fun x => lt x (num 0)) "`x < 0`",
    adj phrase!"nonnegative" (predR fun x => le (num 0) x) "`x ≥ 0`",
    adj phrase!"nonpositive" (predR fun x => le x (num 0)) "`x ≤ 0`"]

end Leanify.Core

namespace Leanify.Vocab

/-- The core vocabulary: what every article is read with. -/
def core : Vocab := Core.numbers

end Leanify.Vocab
