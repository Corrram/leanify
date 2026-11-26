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
/-- A function of two sequences depends only on the first `n` observations (their terms below `n`). -/
def firstObs : Nat := 35
/-- A function on the square is Borel measurable. -/
def borelSq : Nat := 36

/-- The expectation of a function of the two coordinates for a coupling, and the
condition under which it is defined. -/
def couplingExp : Nat := 37
def couplingInt : Nat := 38
/-- The coupling of a copula (the law of `(1-U,1-V)`), and the copula of a coupling. -/
def couplingOf : Nat := 39
def copulaOf : Nat := 40
/-- A map of `[0,1]` preserves Lebesgue measure. -/
def lebPreserving : Nat := 41
/-- A quantity of functions on the square is affine on a class of them. -/
def affineOn : Nat := 42
/-- Continuous real functions on `[0,1]` and on the square, finite subsets of `[0,1]`. -/
def continuous1 : Nat := 43
def continuous2 : Nat := 44
def finite1 : Nat := 45
/-- The joint law of a random pair `(Y,Z)` of a real random variable and a point of
`[0,1]`: that a set function is such a law, the expectation and integrability of a
function of the pair, almost sure conditions, the distribution function of `Y`, and
that `Z` is uniformly distributed. -/
abbrev rmeas : Ty := (.real ⟶ I01 ⟶ .prop) ⟶ .real
def pairLaw : Nat := 46
def pairExp : Nat := 47
def pairInt : Nat := 48
def pairAe : Nat := 49
def pairDf : Nat := 50
def pairUniform : Nat := 51

/-- A quantity of functions on the unit square (of copulas, say), and a class of them. -/
abbrev Quantity : Ty := sq ⟶ .real
abbrev Class : Ty := sq ⟶ .prop

/-- The words `with respect to uniform convergence`. -/
def uniformly : List Codes := [w!"with", w!"respect", w!"to", w!"uniform", w!"convergence"]

/-- A function on the square is a copula. -/
def isCopula : Tm := .lam sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0)))

/-- A predicate of real functions on `[0,1]`, its function `loc 0` in `body`. -/
def fn1 (body : Tm) : Tm := .lam (I01 ⟶ .real) .tt body

/-- The real number of a point of `[0,1]`. -/
def v1 (x : Tm) : Tm := .app (.const val) x

/-- Monotone (`strict`: strictly; `down`: decreasing) real functions on `[0,1]`. -/
def mono (strict down : Bool) : Tm :=
  let hyp := if strict then Tm.lt (v1 (.loc 1)) (v1 (.loc 0)) else .le (v1 (.loc 1)) (v1 (.loc 0))
  let (a, b) := if down then (Tm.app (.loc 2) (.loc 0), Tm.app (.loc 2) (.loc 1)) else (.app (.loc 2) (.loc 1), .app (.loc 2) (.loc 0))
  fn1 (.all I01 (.all I01 (.imp hyp (if strict then .lt a b else .le a b))))

def vocab : Vocab where
  types := [w!"[0,1]"]
  typeLean := [(w!"Leanify.UnitSquare.Interval", w!"Leanify.UnitSquare.Interval.zero")]
  intervals := [{ lo := 0, hi := 1, ty := I01, val, point, integral, integrable, measurable1, measurable2, lebesgue,
                  integral2 := some integral2, integrable2 := some integrable2, ae2 := some ae2,
                  markovPower := some markovPower, markovDom := some isCopula,
                  sampleExp := some sampleExp, sampleInt := some sampleInt,
                  sampleProb := some sampleProb, sampleEvent := some sampleEvent,
                  firstObs := some firstObs,
                  couplingExp := some couplingExp, couplingInt := some couplingInt,
                  pairLaw := some pairLaw, pairExp := some pairExp, pairInt := some pairInt,
                  pairAe := some pairAe, pairDf := some pairDf, pairUniform := some pairUniform }]
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
    I01 ⟶ .real,
    -- functions of the first observations, Borel functions on the square
    (seq ⟶ seq ⟶ .real) ⟶ .real ⟶ .prop, sq ⟶ .prop,
    -- couplings: the expectation, the coupling of a copula and the copula of a coupling
    meas2 ⟶ sq ⟶ .real, meas2 ⟶ sq ⟶ .prop, sq ⟶ meas2, meas2 ⟶ sq,
    -- maps that preserve Lebesgue measure, affine quantities
    self ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    -- continuous functions on the interval and on the square, finite sets of points
    (I01 ⟶ .real) ⟶ .prop, sq ⟶ .prop, set1 ⟶ .prop,
    -- random pairs: the joint law of a real random variable and a point of `[0,1]`
    rmeas ⟶ .prop, rmeas ⟶ (.real ⟶ I01 ⟶ .real) ⟶ .real, rmeas ⟶ (.real ⟶ I01 ⟶ .real) ⟶ .prop,
    rmeas ⟶ (.real ⟶ I01 ⟶ .prop) ⟶ .prop, rmeas ⟶ .real ⟶ .real, rmeas ⟶ .prop]
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
    w!"h_{#}", w!"\\Phi^{-1}", w!"\\operatorname{FirstObs}(#1,#2)", w!"\\operatorname{Borel}",
    w!"\\mathbb{E}_{#1}\\bigl[#2\\bigr]", w!"\\operatorname{Int}_{#1}(#2)",
    w!"\\operatorname{coupling}(#)", w!"\\operatorname{copula}(#)", w!"\\operatorname{LebPreserving}",
    w!"\\operatorname{affine}(#1)\\text{ on }#2",
    w!"\\operatorname{Continuous}", w!"\\operatorname{Continuous}", w!"\\operatorname{Finite}",
    w!"\\operatorname{Law}", w!"\\mathbb{E}_{#1}\\bigl[#2\\bigr]", w!"\\operatorname{Int}_{#1}(#2)",
    w!"\\operatorname{a.s.}_{#1}(#2)", w!"F_{#}", w!"\\operatorname{UniformSecond}"]
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
    w!"Leanify.UnitSquare.conditionalDF", w!"Leanify.UnitSquare.normalQuantile",
    w!"Leanify.UnitSquare.dependsOnFirst", w!"Leanify.UnitSquare.measurableSq",
    w!"Leanify.UnitSquare.couplingExpectation", w!"Leanify.UnitSquare.couplingIntegrable",
    w!"Leanify.UnitSquare.couplingOfCopula", w!"Leanify.UnitSquare.copulaOfCoupling",
    w!"Leanify.UnitSquare.lebesguePreserving", w!"Leanify.Prelude.affineOnSq",
    w!"Leanify.UnitSquare.continuousOnInterval", w!"Leanify.UnitSquare.continuousOnSquare",
    w!"Leanify.UnitSquare.finiteSet1",
    w!"Leanify.UnitSquare.jointLaw", w!"Leanify.UnitSquare.jointExpectation",
    w!"Leanify.UnitSquare.jointIntegrable", w!"Leanify.UnitSquare.jointAlmostSurely",
    w!"Leanify.UnitSquare.jointDistFn", w!"Leanify.UnitSquare.jointUniformSecond"]
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
    { words := [w!"affine"], ty := Quantity, pred := .const affineOn, onDomain := true,
      doc := "`A((1-t)C₁ + tC₂) = (1-t)A(C₁) + tA(C₂)` for the members `C₁`, `C₂` of the class and `t ∈ [0,1]`" },
    { words := [w!"convex"], ty := Class, pred := .const 9,
      doc := "`Convex ℝ`, for the pointwise vector space structure" },
    { words := [w!"compact"] ++ uniformly, ty := Class, pred := .const 10,
      doc := "`IsCompact` for the topology of uniform convergence on `[0,1]²`" },
    { words := [w!"closed"] ++ uniformly, ty := Class, pred := .const 11,
      doc := "`IsClosed` for the topology of uniform convergence on `[0,1]²`" }]
  nouns := [
    { sing := phrase!"fixed point", plural := phrase!"fixed points", ty := I01,
      pred := .lam I01 .tt .tt, arg := some ([w!"of"], self, .lam self .tt (.lam I01 .tt (.eq (.app (.loc 1) (.loc 0)) (.loc 0)))),
      doc := "a point `x` of `[0,1]` with `f(x) = x`, of a map `f` of `[0,1]` (Mathlib `Function.IsFixedPt`)" },
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
    -- a coupling (of two uniform random variables): a probability measure on `[0,1]^2` with
    -- uniform marginals
    { sing := phrase!"coupling", plural := phrase!"couplings", ty := meas2,
      pred := .lam meas2 .tt (.and (.app (.const probMeasure) (.loc 0)) (.app (.const measUniform) (.loc 0))),
      doc := "a probability measure on `[0,1]²` with uniform marginals: the law of a pair `(X,Z)` of uniform random variables" },
    { sing := phrase!"finite subset $v$ of $[0,1]$", plural := phrase!"finite subsets $v$ of $[0,1]$", ty := set1,
      pred := .lam set1 .tt (.app (.const finite1) (.loc 0)),
      doc := "a finite set of points of `[0,1]` (Mathlib `Set.Finite`)" },
    { sing := phrase!"Borel set", plural := phrase!"Borel sets", ty := set1,
      pred := .lam set1 .tt (.app (.const measurable1) (.loc 0)),
      doc := "a Borel subset of `[0,1]` (Mathlib `MeasurableSet`)" },
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
    { name := phrase!"coupling associated with $v$", value := .const couplingOf, ty := sq ⟶ meas2,
      doms := [some isCopula],
      doc := "the law of `(X,Z) = (1-U,1-V)` for a pair `(U,V)` with the copula `C`: `γ(A) = μ_C{(u,v) : (1-u,1-v) ∈ A}`" },
    { name := phrase!"copula associated with $v$", value := .const copulaOf, ty := meas2 ⟶ sq,
      doms := [some (.lam meas2 .tt (.and (.app (.const probMeasure) (.loc 0)) (.app (.const measUniform) (.loc 0))))],
      doc := "the copula of `(U,V) = (1-X,1-Z)` for a pair `(X,Z)` with the coupling `γ`: `C(u,v) = γ{(x,z) : x ≥ 1-u, z ≥ 1-v}`" },
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
    { phrase := phrase!"continuous", prenominal := true, ty := I01 ⟶ .real,
      pred := .lam (I01 ⟶ .real) .tt (.app (.const continuous1) (.loc 0)),
      doc := "a continuous real function on `[0,1]` (Mathlib `Continuous`)" },
    { phrase := phrase!"uniformly continuous", prenominal := true, ty := I01 ⟶ .real,
      pred := fn1 (.all .real (.imp (.lt (.num 0) (.loc 0)) (.ex .real (.and (.lt (.num 0) (.loc 0))
        (.all I01 (.all I01 (.imp (.lt (.abs (.sub (v1 (.loc 1)) (v1 (.loc 0)))) (.loc 2))
          (.lt (.abs (.sub (.app (.loc 4) (.loc 1)) (.app (.loc 4) (.loc 0)))) (.loc 3))))))))),
      doc := "for every `ε > 0` a `δ > 0` with `|f(x) - f(y)| < ε` where `|x - y| < δ` (Mathlib `UniformContinuous`)" },
    { phrase := phrase!"Lipschitz", prenominal := true, ty := I01 ⟶ .real,
      pred := fn1 (.ex .real (.and (.le (.num 0) (.loc 0)) (.all I01 (.all I01
        (.le (.abs (.sub (.app (.loc 3) (.loc 1)) (.app (.loc 3) (.loc 0)))) (.mul (.loc 2) (.abs (.sub (v1 (.loc 1)) (v1 (.loc 0)))))))))),
      doc := "`|f(x) - f(y)| ≤ L|x - y|` for some `L ≥ 0` (Mathlib `LipschitzWith`)" },
    { phrase := phrase!"constant", prenominal := true, ty := I01 ⟶ .real,
      pred := fn1 (.all I01 (.all I01 (.eq (.app (.loc 2) (.loc 1)) (.app (.loc 2) (.loc 0))))),
      doc := "`f(x) = f(y)` for all `x`, `y`" },
    { phrase := phrase!"bounded", prenominal := true, ty := I01 ⟶ .real,
      pred := fn1 (.ex .real (.all I01 (.le (.abs (.app (.loc 2) (.loc 0))) (.loc 1)))),
      doc := "`|f(x)| ≤ M` for some `M` and all `x`" },
    { phrase := phrase!"positive", prenominal := true, ty := I01 ⟶ .real,
      pred := fn1 (.all I01 (.lt (.num 0) (.app (.loc 1) (.loc 0)))), doc := "`f(x) > 0` for all `x`" },
    { phrase := phrase!"nonnegative", prenominal := true, ty := I01 ⟶ .real,
      pred := fn1 (.all I01 (.le (.num 0) (.app (.loc 1) (.loc 0)))), doc := "`f(x) ≥ 0` for all `x`" },
    { phrase := phrase!"increasing", prenominal := true, ty := I01 ⟶ .real, pred := mono false false,
      doc := "`f(x) ≤ f(y)` for `x ≤ y` (Mathlib `Monotone`)" },
    { phrase := phrase!"nondecreasing", prenominal := true, ty := I01 ⟶ .real, pred := mono false false,
      doc := "`f(x) ≤ f(y)` for `x ≤ y` (Mathlib `Monotone`)" },
    { phrase := phrase!"strictly increasing", prenominal := true, ty := I01 ⟶ .real, pred := mono true false,
      doc := "`f(x) < f(y)` for `x < y` (Mathlib `StrictMono`)" },
    { phrase := phrase!"decreasing", prenominal := true, ty := I01 ⟶ .real, pred := mono false true,
      doc := "`f(x) ≥ f(y)` for `x ≤ y` (Mathlib `Antitone`)" },
    { phrase := phrase!"nonincreasing", prenominal := true, ty := I01 ⟶ .real, pred := mono false true,
      doc := "`f(x) ≥ f(y)` for `x ≤ y` (Mathlib `Antitone`)" },
    { phrase := phrase!"strictly decreasing", prenominal := true, ty := I01 ⟶ .real, pred := mono true true,
      doc := "`f(x) > f(y)` for `x < y` (Mathlib `StrictAnti`)" },
    { phrase := phrase!"continuous", prenominal := true, ty := self,
      pred := .lam self .tt (.app (.const continuous1) (.lam I01 .tt (.app (.const val) (.app (.loc 1) (.loc 0))))),
      doc := "a continuous map of `[0,1]` to itself (Mathlib `Continuous`)" },
    { phrase := phrase!"continuous", prenominal := true, ty := sq,
      pred := .lam sq .tt (.app (.const continuous2) (.loc 0)),
      doc := "a continuous real function on the square `[0,1]²` (Mathlib `Continuous` of the uncurried function)" },
    { phrase := phrase!"Lebesgue measure preserving", prenominal := true, ty := self,
      pred := .lam self .tt (.app (.const lebPreserving) (.loc 0)),
      doc := "a Borel measurable map `T` of `[0,1]` with `Leb(T⁻¹(B)) = Leb(B)` for every Borel set `B` (Mathlib `MeasurePreserving`)" },
    { phrase := phrase!"Borel measurable", prenominal := true, ty := self,
      pred := .lam self .tt (.app (.const borel) (.loc 0)),
      doc := "a Borel measurable map of `[0,1]` (Mathlib `Measurable`)" },
    { phrase := phrase!"Borel measurable", prenominal := true, ty := sq,
      pred := .lam sq .tt (.app (.const borelSq) (.loc 0)),
      doc := "a Borel measurable real function on the square `[0,1]²` (Mathlib `Measurable` of the uncurried function)" },
    { phrase := phrase!"Borel measurable", prenominal := true, ty := I01 ⟶ I01 ⟶ I01,
      pred := .lam (I01 ⟶ I01 ⟶ I01) .tt (.app (.const borelSq)
        (.lam I01 .tt (.lam I01 .tt (.app (.const val) (.app (.app (.loc 2) (.loc 1)) (.loc 0)))))),
      doc := "a Borel measurable map of the square `[0,1]²` to `[0,1]` (Mathlib `Measurable` of the uncurried function, as a real function)" },
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
