import Leanify.Vocab

/-! # Vocabulary: probability on the unit square

Distribution functions and probability measures on `[0,1]^2`, uniform
marginals, and (bivariate) copulas: distribution functions on `[0,1]^2` with
uniform marginals. The meanings of the four constants are given in
`Leanify.Library.UnitSquareModel` (`UnitSquare.model`). -/

namespace Leanify.UnitSquare

/-- Constant indices (in this vocabulary). -/
def distFn : Nat := 0
def distFnUniform : Nat := 1
def probMeasure : Nat := 2
def measUniform : Nat := 3

def vocab : Vocab where
  consts := [Ty.sq ⟶ .prop, Ty.sq ⟶ .prop, Ty.meas2 ⟶ .prop, Ty.meas2 ⟶ .prop]
  constNames := [w!"\\operatorname{DistFn}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{Prob}_{[0,1]^2}", w!"\\operatorname{UnifMarg}"]
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
