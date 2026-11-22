import Leanify.Library.Core

/-! # Vocabulary: probability on the unit square

The interval `[0,1]` as a type of its own (`Vocab.intervals`): its points, the integral
`\int_0^1` and Lebesgue measure on it, and Borel measurable maps of it. On it:
distribution functions and probability measures on `[0,1]^2`, the integral against
the measure of a distribution function (`\int_{[0,1]^2} f(u,v)\,\mathrm{d}C(u,v)`), uniform
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
/-- The integral of a function on the square against the probability measure with a
given distribution function, and the condition under which it is defined. -/
def integral2 : Nat := 20
def integrable2 : Nat := 21
/-- Borel measurable real functions on `[0,1]`. -/
def borelReal : Nat := 22
/-- A condition holds at almost every point of the square, for the measure of a
distribution function. -/
def ae2 : Nat := 23
/-- The Markov product of two functions on the square, and the Markov power of one. -/
def markovProduct : Nat := 24
def markovPower : Nat := 25
/-- The expectation and the probability for a sample of independent observations with a
given distribution function, and the conditions under which they are defined. -/
def sampleExp : Nat := 26
def sampleInt : Nat := 27
def sampleProb : Nat := 28
def sampleEvent : Nat := 29
/-- A sequence of points of `[0,1]` (used at the indices `0, 1, 2, …`). -/
def seq : Ty := .real ⟶ I01
/-- A kernel: a square-integrable function of finitely many terms of a sequence. -/
def kernel : Nat := 30
/-- A statistic: a measurable function of finitely many observations of a sample. -/
def statistic : Nat := 31
/-- A function on the square with a bounded density. -/
def boundedDensity : Nat := 32
/-- The conditional distribution function of the second coordinate given the first, for
the measure of a distribution function. -/
def condDF : Nat := 33
/-- The quantile function of the standard normal distribution, on `[0,1]`. -/
def normalQ : Nat := 34

/-- A quantity of functions on the unit square (of copulas, say), and a class of them. -/
abbrev Quantity : Ty := sq ⟶ .real
abbrev Class : Ty := sq ⟶ .prop

/-- The words `with respect to uniform convergence`. -/
def uniformly : List Codes := [w!"with", w!"respect", w!"to", w!"uniform", w!"convergence"]

/-- A function on the square is a copula. -/
def isCopula : Tm := .lam sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0)))

def vocab : Vocab where
  types := [w!"[0,1]"]
  typeLean := [(w!"Leanify.UnitSquare.Interval", w!"Leanify.UnitSquare.Interval.zero")]
  intervals := [{ lo := 0, hi := 1, ty := I01, val, point, integral, integrable, measurable1, measurable2, lebesgue,
                  integral2 := some integral2, integrable2 := some integrable2, ae2 := some ae2,
                  markovPower := some markovPower, markovDom := some isCopula,
                  sampleExp := some sampleExp, sampleInt := some sampleInt,
                  sampleProb := some sampleProb, sampleEvent := some sampleEvent }]
  consts := [sq ⟶ .prop, sq ⟶ .prop, meas2 ⟶ .prop, meas2 ⟶ .prop,
    -- properties of a quantity on a class, and of a class
    Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    Class ⟶ .prop, Class ⟶ .prop, Class ⟶ .prop,
    -- the type `[0,1]`
    I01 ⟶ .real, .real ⟶ I01, (I01 ⟶ .real) ⟶ .real, (I01 ⟶ .real) ⟶ .prop,
    set1 ⟶ .prop, set2 ⟶ .prop, set1 ⟶ .real, self ⟶ .prop,
    -- the integral against the measure of a distribution function
    sq ⟶ sq ⟶ .real, sq ⟶ sq ⟶ .prop, (I01 ⟶ .real) ⟶ .prop,
    sq ⟶ (I01 ⟶ I01 ⟶ .prop) ⟶ .prop,
    -- the Markov product and the Markov powers
    sq ⟶ sq ⟶ sq, sq ⟶ .real ⟶ sq,
    -- the expectation and the probability for a sample
    sq ⟶ (seq ⟶ seq ⟶ .real) ⟶ .real, sq ⟶ (seq ⟶ seq ⟶ .real) ⟶ .prop,
    sq ⟶ (seq ⟶ seq ⟶ .prop) ⟶ .real, sq ⟶ (seq ⟶ seq ⟶ .prop) ⟶ .prop,
    (seq ⟶ .real) ⟶ .prop, (seq ⟶ seq ⟶ .real) ⟶ .prop, sq ⟶ .prop,
    -- the conditional distribution function
    sq ⟶ sq,
    -- the standard normal quantile function
    I01 ⟶ .real]
  constNames := [w!"\\operatorname{DistFn}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{Prob}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{convex}(#1)\\text{ on }#2", w!"\\operatorname{concave}(#1)\\text{ on }#2",
    w!"\\operatorname{lsc\\ (uniform)}(#1)\\text{ on }#2", w!"\\operatorname{usc\\ (uniform)}(#1)\\text{ on }#2",
    w!"\\operatorname{continuous\\ (uniform)}(#1)\\text{ on }#2",
    w!"\\operatorname{convex}", w!"\\operatorname{compact\\ (uniform)}", w!"\\operatorname{closed\\ (uniform)}",
    w!"", w!"\\langle #\\rangle_{[0,1]}", w!"\\int_0^1", w!"\\operatorname{Int}",
    w!"\\operatorname{Meas}", w!"\\operatorname{Meas}", w!"\\lambda\\bigl(#\\bigr)", w!"\\operatorname{Borel}",
    w!"\\int_{[0,1]^2}", w!"\\operatorname{Int}_{\\mathrm{d}#1}(#2)", w!"\\operatorname{Borel}",
    w!"\\operatorname{a.e.}_{\\mathrm{d}#1}(#2)",
    w!"#1\\ast #2", w!"{#1}^{\\ast #2}",
    w!"\\mathbb{E}_{#1}\\bigl[#2\\bigr]", w!"\\operatorname{Int}_{#1}(#2)",
    w!"P_{#1}\\bigl(#2\\bigr)", w!"\\operatorname{Event}_{#1}(#2)",
    w!"\\operatorname{Kernel}", w!"\\operatorname{Statistic}", w!"\\operatorname{BddDensity}",
    w!"h_{#}", w!"\\Phi^{-1}"]
  constLean := [w!"Leanify.UnitSquare.distFn2", w!"Leanify.UnitSquare.dfUniformMarginals",
    w!"Leanify.UnitSquare.probMeasure2", w!"Leanify.UnitSquare.measUniformMarginals",
    w!"Leanify.Prelude.convexOnSq", w!"Leanify.Prelude.concaveOnSq", w!"Leanify.Prelude.lscUniform",
    w!"Leanify.Prelude.uscUniform", w!"Leanify.Prelude.continuousUniform",
    w!"Leanify.Prelude.convexClass", w!"Leanify.Prelude.compactUniform", w!"Leanify.Prelude.closedUniform",
    w!"Leanify.UnitSquare.Interval.val", w!"Leanify.UnitSquare.Interval.point", w!"Leanify.UnitSquare.Interval.integral",
    w!"Leanify.Prelude.integrable", w!"Leanify.Prelude.measurableSet1", w!"Leanify.Prelude.measurableSet2",
    w!"Leanify.Prelude.leb", w!"Leanify.UnitSquare.Interval.borel",
    w!"Leanify.UnitSquare.integralAgainst", w!"Leanify.UnitSquare.integrableAgainst",
    w!"Leanify.UnitSquare.Interval.borelReal", w!"Leanify.UnitSquare.aeAgainst",
    w!"Leanify.UnitSquare.markovProd", w!"Leanify.UnitSquare.markovPowerOf",
    w!"Leanify.UnitSquare.sampleExpectation", w!"Leanify.UnitSquare.sampleIntegrable",
    w!"Leanify.UnitSquare.sampleProbability", w!"Leanify.UnitSquare.sampleHasProbability",
    w!"Leanify.UnitSquare.isKernel", w!"Leanify.UnitSquare.isStatistic", w!"Leanify.UnitSquare.hasBoundedDensity",
    w!"Leanify.UnitSquare.conditionalDF", w!"Leanify.UnitSquare.normalQuantile"]
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
      doc := "a distribution function on `[0,1]²` with uniform marginals" },
    { sing := phrase!"sequence $v$ in $[0,1]$", plural := phrase!"sequences $v$ in $[0,1]$", ty := seq,
      pred := .lam seq .tt .tt,
      doc := "a sequence of points of `[0,1]`: its terms are those at the indices `0, 1, 2, …`" },
    { sing := phrase!"kernel", plural := phrase!"kernels", ty := seq ⟶ .real,
      pred := .lam (seq ⟶ .real) .tt (.app (.const kernel) (.loc 0)),
      doc := "a Borel function of the terms `1, …, m` of a sequence in `[0,1]` for some `m` (a function on `[0,1]^m`), square-integrable for independent uniform terms" },
    { sing := phrase!"statistic", plural := phrase!"statistics", ty := seq ⟶ seq ⟶ .real,
      pred := .lam (seq ⟶ seq ⟶ .real) .tt (.app (.const statistic) (.loc 0)),
      doc := "a real function of finitely many observations `(U_i,V_i)` of a sample, measurable in them" }]
  notions := [
    { name := phrase!"Lebesgue measure on $[0,1]$", value := .const lebesgue, ty := set1 ⟶ .real,
      doc := "the Lebesgue measure of a subset of `[0,1]` (Mathlib `volume`)" },
    { name := phrase!"standard normal quantile function", value := .const normalQ, ty := I01 ⟶ .real,
      doc := "`Φ⁻¹(u) = inf {x : u ≤ Φ(x)}` for the standard normal distribution function `Φ` (Mathlib `cdf (gaussianReal 0 1)`): the inverse of `Φ` on `(0,1)`" },
    { name := phrase!"conditional distribution function of $v$", value := .const condDF, ty := sq ⟶ sq,
      doms := [some isCopula],
      doc := "`h_C(u,v) = P(V ≤ v | U = u)` for a copula `C`, the distribution function of `(U,V)`: the conditional distribution function of `V` given `U = u`, from the disintegration of the measure of `C` (Mathlib `Measure.condKernel`); a version of `∂₁C`" },
    { name := phrase!"Markov product of $v$ and $v$", value := .const markovProduct, ty := sq ⟶ sq ⟶ sq,
      doms := [some isCopula, some isCopula],
      doc := "`(A*B)(u,v) = ∫₀¹ ∂₂A(u,t) ∂₁B(t,v) dt` for copulas `A`, `B` (Darsow, Nguyen and Olsen): the copula of `(X₀,X₂)` for a Markov chain whose steps have the copulas `A` and `B`" },
    { name := phrase!"Markov power of order $v$ of $v$",
      value := .lam .real .tt (.lam sq .tt (.app (.app (.const markovPower) (.loc 0)) (.loc 1))),
      ty := .real ⟶ sq ⟶ sq,
      doms := [some (.lam .real .tt (.and (.app (.prim .isNat) (.loc 0)) (.le (.num 1) (.loc 0)))), some isCopula],
      doc := "the Markov product of `k` factors `C`, for an integer `k ≥ 1` and a copula `C`: the copula of `(X₀,X_k)` for a stationary Markov chain whose steps have the copula `C`" }]
  mods := [
    { phrase := phrase!"with bounded density", prenominal := false, ty := sq,
      pred := .lam sq .tt (.app (.const boundedDensity) (.loc 0)),
      doc := "an absolutely continuous function on the square whose density is bounded: `C(u,v) = ∫₀ᵘ∫₀ᵛ c` for a bounded measurable `c`" },
    { phrase := phrase!"symmetric", prenominal := true, ty := sq,
      pred := .lam sq .tt (.all I01 (.all I01 (.eq (.app (.app (.loc 2) (.loc 1)) (.loc 0))
        (.app (.app (.loc 2) (.loc 0)) (.loc 1))))),
      doc := "a function `C` on the square with `C(u,v) = C(v,u)` for all `u`, `v` (a copula that equals its transpose)" },
    { phrase := phrase!"Borel measurable", prenominal := true, ty := self,
      pred := .lam self .tt (.app (.const borel) (.loc 0)),
      doc := "a Borel measurable map of `[0,1]` (Mathlib `Measurable`)" },
    { phrase := phrase!"Borel measurable", prenominal := true, ty := I01 ⟶ .real,
      pred := .lam (I01 ⟶ .real) .tt (.app (.const borelReal) (.loc 0)),
      doc := "a Borel measurable real function on `[0,1]` (Mathlib `Measurable`)" },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := sq, pred := .const 1,
      doc := "`F(u,1) = u`, `F(1,v) = v`" },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := meas2, pred := .const 3,
      doc := "`γ([0,u]×[0,1]) = u`, `γ([0,1]×[0,v]) = v`" }]

/-- The core vocabulary followed by this one: what an article about probability on
the unit square is compiled with. -/
def withCore : Vocab := Vocab.core ++ vocab

end Leanify.UnitSquare
