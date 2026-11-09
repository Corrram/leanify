import Leanify.Vocab

/-! # Vocabulary: probability on the unit square

Distribution functions and probability measures on `[0,1]^2`, uniform
marginals, and (bivariate) copulas: distribution functions on `[0,1]^2` with
uniform marginals; and properties of a quantity of such functions on a class of them
(convexity, semicontinuity and continuity for uniform convergence) and of such a class.
Each constant names its Lean meaning, a definition of
`Leanify.Library.UnitSquareModel`. -/

namespace Leanify.UnitSquare

/-- Constant indices (in this vocabulary). -/
def distFn : Nat := 0
def distFnUniform : Nat := 1
def probMeasure : Nat := 2
def measUniform : Nat := 3

/-- A quantity of functions on the unit square (of copulas, say), and a class of them. -/
abbrev Quantity : Ty := Ty.sq ⟶ .real
abbrev Class : Ty := Ty.sq ⟶ .prop

/-- The words `with respect to uniform convergence`. -/
def uniformly : List Codes := [w!"with", w!"respect", w!"to", w!"uniform", w!"convergence"]

def vocab : Vocab where
  consts := [Ty.sq ⟶ .prop, Ty.sq ⟶ .prop, Ty.meas2 ⟶ .prop, Ty.meas2 ⟶ .prop,
    -- properties of a quantity on a class, and of a class
    Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    Quantity ⟶ Class ⟶ .prop, Quantity ⟶ Class ⟶ .prop,
    Class ⟶ .prop, Class ⟶ .prop, Class ⟶ .prop]
  constNames := [w!"\\operatorname{DistFn}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{Prob}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{convex}(#1)\\text{ on }#2", w!"\\operatorname{concave}(#1)\\text{ on }#2",
    w!"\\operatorname{lsc\\ (uniform)}(#1)\\text{ on }#2", w!"\\operatorname{usc\\ (uniform)}(#1)\\text{ on }#2",
    w!"\\operatorname{continuous\\ (uniform)}(#1)\\text{ on }#2",
    w!"\\operatorname{convex}", w!"\\operatorname{compact\\ (uniform)}", w!"\\operatorname{closed\\ (uniform)}"]
  constLean := [w!"Leanify.UnitSquare.distFn2", w!"Leanify.UnitSquare.dfUniformMarginals",
    w!"Leanify.UnitSquare.probMeasure2", w!"Leanify.UnitSquare.measUniformMarginals",
    w!"Leanify.Prelude.convexOnSq", w!"Leanify.Prelude.concaveOnSq", w!"Leanify.Prelude.lscUniform",
    w!"Leanify.Prelude.uscUniform", w!"Leanify.Prelude.continuousUniform",
    w!"Leanify.Prelude.convexClass", w!"Leanify.Prelude.compactUniform", w!"Leanify.Prelude.closedUniform"]
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
      plural := phrase!"distribution functions on $[0,1]^2$", ty := Ty.sq, pred := .const 0,
      doc := "`(u,v) ↦ μ([0,u]×[0,v])` for a probability measure `μ` on `[0,1]²`" },
    { sing := phrase!"probability measure $v$ on $[0,1]^2$",
      plural := phrase!"probability measures $v$ on $[0,1]^2$", ty := Ty.meas2, pred := .const 2,
      doc := "agrees with a probability measure (Mathlib `IsProbabilityMeasure`) on measurable sets" },
    -- a (bivariate) copula: a distribution function on `[0,1]^2` with uniform marginals
    { sing := phrase!"bivariate copula", plural := phrase!"bivariate copulas", ty := Ty.sq,
      pred := .lam Ty.sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0))),
      doc := "a distribution function on `[0,1]²` with uniform marginals" },
    { sing := phrase!"copula", plural := phrase!"copulas", ty := Ty.sq,
      pred := .lam Ty.sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0))),
      doc := "a distribution function on `[0,1]²` with uniform marginals" }]
  mods := [
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.sq, pred := .const 1,
      doc := "`F(u,1) = u`, `F(1,v) = v`" },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.meas2, pred := .const 3,
      doc := "`γ([0,u]×[0,1]) = u`, `γ([0,1]×[0,v]) = v`" }]

/-- The core vocabulary followed by this one: what an article about probability on
the unit square is compiled with. -/
def withCore : Vocab := Vocab.core ++ vocab

end Leanify.UnitSquare
