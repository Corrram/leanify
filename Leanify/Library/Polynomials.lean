import Leanify.Library.Core

/-! # Vocabulary: polynomials

A polynomial is a real function that is given by a polynomial with real coefficients
(`p(x) = a_0 + a_1x + … + a_nx^n` for every real `x`), so that an article writes `p(x)`,
`p+q`, `pq` and `p'` as for any real function. The polynomial of such a function is unique,
and the notions of the field are those of it: the degree (`\deg p`, defined for a nonzero
polynomial), the leading coefficient, the coefficients, the real roots and their
multiplicities; polynomials with integer or rational coefficients, monic, quadratic, cubic
and irreducible polynomials.

The constants are interpreted by `Leanify/Library/PolynomialsModel.lean`, through Mathlib's
`Polynomial ℝ`. -/

namespace Leanify.Polynomials
open Build Core

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def isPoly : Nat := 0
def degree : Nat := 1
def leadingCoeff : Nat := 2
def coeff : Nat := 3
def numRoots : Nat := 4
def intCoeffs : Nat := 5
def ratCoeffs : Nat := 6
def monic : Nat := 7
def irreducibleQ : Nat := 8
def irreducibleR : Nat := 9
def rootMult : Nat := 10
end Const
open Const

def poly (f : B) : B := app (const isPoly) f

/-- A polynomial that is not the zero polynomial. -/
def nonzeroPoly : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f =>
  and (poly f) (not (allR fun x => eq (app f x) (num 0)))

def polyPred : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f => poly f

/-- A polynomial of degree `d`. -/
def ofDegree (d : Nat) : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f =>
  and (and (poly f) (not (allR fun x => eq (app f x) (num 0)))) (eq (app (const degree) f) (num d))

def nonconstant : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f =>
  and (and (poly f) (not (allR fun x => eq (app f x) (num 0)))) (le (num 1) (app (const degree) f))

def withPoly (c : Nat) : Tm := close <| lamT Ty.rfun (fun _ => tt) fun f => and (poly f) (app (const c) f)

def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := Ty.rfun, pred, doc }

def nounP (sing plural : Phrase) : Noun :=
  { sing, plural, ty := Ty.rfun, pred := polyPred,
    doc := "a real function given by a polynomial with real coefficients (Mathlib `Polynomial.eval`)" }

def vocab : Vocab where
  consts := [Ty.rfun ⟶ .prop, Ty.rfun ⟶ .real, Ty.rfun ⟶ .real, .real ⟶ Ty.rfun ⟶ .real, Ty.rfun ⟶ .real,
    Ty.rfun ⟶ .prop, Ty.rfun ⟶ .prop, Ty.rfun ⟶ .prop, Ty.rfun ⟶ .prop, Ty.rfun ⟶ .prop,
    .real ⟶ Ty.rfun ⟶ .real]
  constNames := [w!"\\operatorname{IsPoly}", w!"\\deg", w!"\\operatorname{lc}", w!"\\operatorname{coeff}_{#1}(#2)",
    w!"\\operatorname{\\#roots}", w!"\\operatorname{IntCoeffs}", w!"\\operatorname{RatCoeffs}",
    w!"\\operatorname{Monic}", w!"\\operatorname{Irreducible}_{\\mathbb{Q}}", w!"\\operatorname{Irreducible}_{\\mathbb{R}}",
    w!"\\operatorname{mult}_{#1}(#2)"]
  constLean := [w!"Leanify.Polynomials.IsPoly", w!"Leanify.Polynomials.degree", w!"Leanify.Polynomials.leadingCoeff",
    w!"Leanify.Polynomials.coeff", w!"Leanify.Polynomials.numRoots", w!"Leanify.Polynomials.IntCoeffs",
    w!"Leanify.Polynomials.RatCoeffs", w!"Leanify.Polynomials.Monic", w!"Leanify.Polynomials.IrreducibleQ",
    w!"Leanify.Polynomials.IrreducibleR", w!"Leanify.Polynomials.rootMultiplicity"]
  modules := [w!"Leanify.Library.PolynomialsModel"]
  nouns := [
    nounP phrase!"polynomial" phrase!"polynomials",
    nounP phrase!"polynomial function" phrase!"polynomial functions",
    nounP phrase!"real polynomial" phrase!"real polynomials"]
  mods := [
    -- (`$f\colon\mathbb{R}\to\mathbb{R}$ be a polynomial function`: the function of the signature)
    mod phrase!"polynomial" true polyPred "given by a polynomial with real coefficients (Mathlib `Polynomial.eval`)",
    mod phrase!"monic" true (withPoly monic) "leading coefficient 1 (Mathlib `Polynomial.Monic`)",
    mod phrase!"with a real root" false (close <| lamT Ty.rfun (fun _ => tt) fun f => and (poly f) (exR fun x => eq (app f x) (num 0)))
      "`p(x) = 0` for some real `x`",
    mod phrase!"without real roots" false (close <| lamT Ty.rfun (fun _ => tt) fun f => and (poly f) (allR fun x => not (eq (app f x) (num 0))))
      "`p(x) ≠ 0` for every real `x` (also `has no real roots`)",
    mod phrase!"without real root" false (close <| lamT Ty.rfun (fun _ => tt) fun f => and (poly f) (allR fun x => not (eq (app f x) (num 0))))
      "`p(x) ≠ 0` for every real `x`",
    mod phrase!"without a real root" false (close <| lamT Ty.rfun (fun _ => tt) fun f => and (poly f) (allR fun x => not (eq (app f x) (num 0))))
      "`p(x) ≠ 0` for every real `x`",
    mod phrase!"quadratic" true (ofDegree 2) "a polynomial of degree 2",
    mod phrase!"cubic" true (ofDegree 3) "a polynomial of degree 3",
    mod phrase!"quartic" true (ofDegree 4) "a polynomial of degree 4",
    mod phrase!"nonconstant" true nonconstant "a polynomial of degree at least 1",
    mod phrase!"irreducible over $\\mathbb{Q}$" true (withPoly irreducibleQ)
      "with rational coefficients, and irreducible in `ℚ[X]` (Mathlib `Irreducible`)",
    mod phrase!"irreducible over $\\mathbb{R}$" true (withPoly irreducibleR)
      "irreducible in `ℝ[X]` (Mathlib `Irreducible`)",
    mod phrase!"irreducible over $\\mathbb{Q}$" false (withPoly irreducibleQ)
      "with rational coefficients, and irreducible in `ℚ[X]` (Mathlib `Irreducible`)",
    mod phrase!"irreducible over $\\mathbb{R}$" false (withPoly irreducibleR)
      "irreducible in `ℝ[X]` (Mathlib `Irreducible`)",
    mod phrase!"nonzero" true nonzeroPoly "not the zero polynomial",
    mod phrase!"of degree $v$" false (close <| lamR fun n => lamT Ty.rfun (fun _ => tt) fun f =>
        and (and (poly f) (not (allR fun x => eq (app f x) (num 0)))) (eq (app (const degree) f) n))
      "a nonzero polynomial of degree `n`",
    mod phrase!"of degree at most $v$" false (close <| lamR fun n => lamT Ty.rfun (fun _ => tt) fun f =>
        and (poly f) (or (allR fun x => eq (app f x) (num 0)) (le (app (const degree) f) n)))
      "zero, or of degree at most `n`",
    mod phrase!"with real coefficients" false polyPred "a polynomial (Mathlib `Polynomial ℝ`)",
    mod phrase!"with integer coefficients" false (withPoly intCoeffs) "every coefficient is an integer",
    mod phrase!"with rational coefficients" false (withPoly ratCoeffs) "every coefficient is rational"]
  notions := [
    { name := phrase!"degree of $v$", value := .const degree, ty := Ty.rfun ⟶ .real, doms := [some nonzeroPoly],
      doc := "of a nonzero polynomial (Mathlib `Polynomial.natDegree`)" },
    { name := phrase!"leading coefficient of $v$", value := .const leadingCoeff, ty := Ty.rfun ⟶ .real,
      doms := [some nonzeroPoly], doc := "of a nonzero polynomial (Mathlib `Polynomial.leadingCoeff`)" },
    { name := phrase!"constant term of $v$", value := close (lamT Ty.rfun (fun _ => tt) fun f => app f (num 0)),
      ty := Ty.rfun ⟶ .real, doms := [some polyPred], doc := "`p(0)` (Mathlib `Polynomial.coeff p 0`)" },
    { name := phrase!"$v$th coefficient of $v$", value := .const coeff, ty := .real ⟶ Ty.rfun ⟶ .real,
      doms := [some nonnegInt, some polyPred], doc := "the coefficient of `x^k` (Mathlib `Polynomial.coeff`)" },
    { name := phrase!"number of real roots of $v$", value := .const numRoots, ty := Ty.rfun ⟶ .real,
      doms := [some nonzeroPoly], doc := "distinct, of a nonzero polynomial (Mathlib `Polynomial.roots`)" },
    { name := phrase!"number of distinct real roots of $v$", value := .const numRoots, ty := Ty.rfun ⟶ .real,
      doms := [some nonzeroPoly], doc := "of a nonzero polynomial (Mathlib `Polynomial.roots`)" },
    { name := phrase!"set of real roots of $v$", value := close (lamT Ty.rfun (fun _ => tt) fun f =>
        lamR fun x => eq (app f x) (num 0)),
      ty := Ty.rfun ⟶ .real ⟶ .prop, doms := [some polyPred], doc := "`{x ∈ ℝ : p(x) = 0}`" },
    { name := phrase!"multiplicity of $v$ as a root of $v$", value := .const rootMult, ty := .real ⟶ Ty.rfun ⟶ .real,
      doms := [none, some nonzeroPoly], doc := "`0` if it is not a root (Mathlib `Polynomial.rootMultiplicity`)" }]
  symbols := [
    { sym := w!"\\deg", ty := Ty.rfun ⟶ .real, const := some degree, doms := [some nonzeroPoly],
      doc := "the degree of a nonzero polynomial (Mathlib `Polynomial.natDegree`)" }]

end Leanify.Polynomials
