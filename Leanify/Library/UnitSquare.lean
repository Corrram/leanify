import Leanify.Library.Core

/-! # Vocabulary: probability on the unit square

The interval `[0,1]` as a type of its own (`Vocab.intervals`): its points, the integral
`\int_0^1` and Lebesgue measure on it, and Borel measurable maps of it. On it:
distribution functions and probability measures on `[0,1]^2`, uniform
marginals, and (bivariate) copulas: distribution functions on `[0,1]^2` with
uniform marginals; and properties of a quantity of such functions on a class of them
(convexity, semicontinuity and continuity for uniform convergence) and of such a class.
Each constant names its Lean meaning, a declaration of Mathlib or a definition of
`Leanify.Library.UnitSquareModel`.

An article that names this field reads `$u\in[0,1]$` as a point of the type, and
`$C:[0,1]^2\to\mathbb{R}$` as a function of two such points, which has no values outside
the square. Without the field, `[0,1]` is a set of real numbers like `[0,2]`. -/

namespace Leanify.UnitSquare

/-- The type `[0,1]` (the base type of this vocabulary). -/
abbrev I01 : Ty := .base 0
/-- Subsets of the unit interval and of the unit square, as predicates. -/
abbrev set1 : Ty := I01 ⟶ .prop
abbrev set2 : Ty := I01 ⟶ I01 ⟶ .prop
/-- Set functions on the unit square (laws of random pairs). -/
abbrev meas2 : Ty := set2 ⟶ .real
/-- Functions on the unit square, such as distribution functions. -/
abbrev sq : Ty := I01 ⟶ I01 ⟶ .real
/-- Maps of the unit interval. -/
abbrev self : Ty := I01 ⟶ I01

/-- Constant indices (in this vocabulary). -/
def distFn : Nat := 0
def distFnUniform : Nat := 1
def probMeasure : Nat := 2
def measUniform : Nat := 3
/-- The constants of the type `[0,1]`: the number of a point, the point of a number,
the integral and integrability, measurable sets of the interval and of the square,
Lebesgue measure, and Borel measurable maps. -/
def val : Nat := 12
def point : Nat := 13
def integral : Nat := 14
def integrable : Nat := 15
def measurable1 : Nat := 16
def measurable2 : Nat := 17
def lebesgue : Nat := 18
def borel : Nat := 19

/-- A quantity of functions on the unit square (of copulas, say), and a class of them. -/
abbrev Quantity : Ty := sq ⟶ .real
abbrev Class : Ty := sq ⟶ .prop

/-- The words `with respect to uniform convergence`. -/
def uniformly : List Codes := [w!"with", w!"respect", w!"to", w!"uniform", w!"convergence"]

def vocab : Vocab where
  types := [w!"[0,1]"]
  typeLean := [(w!"Leanify.UnitSquare.Interval", w!"Leanify.UnitSquare.Interval.zero")]
  intervals := [{ lo := 0, hi := 1, ty := I01, val, point, integral, integrable, measurable1, measurable2, lebesgue }]
  consts := [sq ⟶ .prop, sq ⟶ .prop, meas2 ⟶ .prop, meas2 ⟶ .prop,
    -- properties of a quantity on a class, and of a class
    Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    Class ⟶ .prop, Class ⟶ .prop, Class ⟶ .prop,
    -- the type `[0,1]`
    I01 ⟶ .real, .real ⟶ I01, (I01 ⟶ .real) ⟶ .real, (I01 ⟶ .real) ⟶ .prop,
    set1 ⟶ .prop, set2 ⟶ .prop, set1 ⟶ .real, self ⟶ .prop]
  constNames := [w!"\\operatorname{DistFn}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{Prob}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{convex}(#1)\\text{ on }#2", w!"\\operatorname{concave}(#1)\\text{ on }#2",
    w!"\\operatorname{lsc\\ (uniform)}(#1)\\text{ on }#2", w!"\\operatorname{usc\\ (uniform)}(#1)\\text{ on }#2",
    w!"\\operatorname{continuous\\ (uniform)}(#1)\\text{ on }#2",
    w!"\\operatorname{convex}", w!"\\operatorname{compact\\ (uniform)}", w!"\\operatorname{closed\\ (uniform)}",
    w!"", w!"\\langle #\\rangle_{[0,1]}", w!"\\int_0^1", w!"\\operatorname{Int}",
    w!"\\operatorname{Meas}", w!"\\operatorname{Meas}", w!"\\lambda\\bigl(#\\bigr)", w!"\\operatorname{Borel}"]
  constLean := [w!"Leanify.UnitSquare.distFn2", w!"Leanify.UnitSquare.dfUniformMarginals",
    w!"Leanify.UnitSquare.probMeasure2", w!"Leanify.UnitSquare.measUniformMarginals",
    w!"Leanify.Prelude.convexOnSq", w!"Leanify.Prelude.concaveOnSq", w!"Leanify.Prelude.lscUniform",
    w!"Leanify.Prelude.uscUniform", w!"Leanify.Prelude.continuousUniform",
    w!"Leanify.Prelude.convexClass", w!"Leanify.Prelude.compactUniform", w!"Leanify.Prelude.closedUniform",
    w!"Leanify.UnitSquare.Interval.val", w!"Leanify.UnitSquare.Interval.point", w!"Leanify.UnitSquare.Interval.integral",
    w!"Leanify.Prelude.integrable", w!"Leanify.Prelude.measurableSet1", w!"Leanify.Prelude.measurableSet2",
    w!"Leanify.Prelude.leb", w!"Leanify.UnitSquare.Interval.borel"]
  modules := [w!"Leanify.Library.UnitSquareModel"]
  adjectives := [
    { words := [w!"convex"], ty := Quantity, pred := .const 4, onDomain := true,
      doc := "`ConvexOn ℝ` on the class, for the pointwise vector space structure" },
    { words := [w!"concave"], ty := Quantity, pred := .const 5, onDomain := true,
      doc := "`ConcaveOn ℝ` on the class" },
    { words := [w!"lower", w!"semicontinuous"] ++ uniformly, ty := Quantity, pred := .const 6, onDomain := true,
      doc := "`LowerSemicontinuousOn` for the topology of uniform convergence on `[0,1]²`" },
    { words := [w!"upper", w!"semicontinuous"] ++ uniformly, ty := Quantity, pred := .const 7, onDomain := true,
      doc := "`UpperSemicontinuousOn` for the topology of uniform convergence on `[0,1]²`" },
    { words := [w!"continuous"] ++ uniformly, ty := Quantity, pred := .const 8, onDomain := true,
      doc := "`ContinuousOn` for the topology of uniform convergence on `[0,1]²`" },
    { words := [w!"convex"], ty := Class, pred := .const 9,
      doc := "`Convex ℝ`, for the pointwise vector space structure" },
    { words := [w!"compact"] ++ uniformly, ty := Class, pred := .const 10,
      doc := "`IsCompact` for the topology of uniform convergence on `[0,1]²`" },
    { words := [w!"closed"] ++ uniformly, ty := Class, pred := .const 11,
      doc := "`IsClosed` for the topology of uniform convergence on `[0,1]²`" }]
  nouns := [
    { sing := phrase!"distribution function on $[0,1]^2$",
      plural := phrase!"distribution functions on $[0,1]^2$", ty := sq, pred := .const 0,
      doc := "`(u,v) ↦ μ([0,u]×[0,v])` for a probability measure `μ` on `[0,1]²`" },
    { sing := phrase!"probability measure $v$ on $[0,1]^2$",
      plural := phrase!"probability measures $v$ on $[0,1]^2$", ty := meas2, pred := .const 2,
      doc := "agrees with a probability measure (Mathlib `IsProbabilityMeasure`) on measurable sets" },
    -- a (bivariate) copula: a distribution function on `[0,1]^2` with uniform marginals
    { sing := phrase!"bivariate copula", plural := phrase!"bivariate copulas", ty := sq,
      pred := .lam sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0))),
      doc := "a distribution function on `[0,1]²` with uniform marginals" },
    { sing := phrase!"copula", plural := phrase!"copulas", ty := sq,
      pred := .lam sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0))),
      doc := "a distribution function on `[0,1]²` with uniform marginals" }]
  notions := [
    { name := phrase!"Lebesgue measure on $[0,1]$", value := .const lebesgue, ty := set1 ⟶ .real,
      doc := "the Lebesgue measure of a subset of `[0,1]` (Mathlib `volume`)" }]
  mods := [
    { phrase := phrase!"Borel measurable", prenominal := true, ty := self,
      pred := .lam self .tt (.app (.const borel) (.loc 0)),
      doc := "a Borel measurable map of `[0,1]` (Mathlib `Measurable`)" },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := sq, pred := .const 1,
      doc := "`F(u,1) = u`, `F(1,v) = v`" },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := meas2, pred := .const 3,
      doc := "`γ([0,u]×[0,1]) = u`, `γ([0,1]×[0,v]) = v`" }]

/-- The core vocabulary followed by this one: what an article about probability on
the unit square is compiled with. -/
def withCore : Vocab := Vocab.core ++ vocab

end Leanify.UnitSquare
