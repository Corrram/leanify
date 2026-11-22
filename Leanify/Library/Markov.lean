import Leanify.Library.Hilbert

/-! # Vocabulary: Markov operators of copulas

The field `markov` extends `hilbert` with the Markov operator of a copula: for a copula `C`
with the conditional distributions `K_C(u,·)` of the second coordinate given the first,
`(T_Cg)(u) = ∫ g(y) K_C(u,\mathrm{d}y) = \mathbb{E}[g(V)\mid U=u]`. An article names it in a
notation, `For a copula $C$, we write $T_C$ for the Markov operator of $C$.`, and then applies
it to functions (`T_Ce_v`), takes its tensor powers (`T_C^{\otimes m}`) and its norm on a class
(`\lVert T_C|_{L^2_0}\rVert`) as the field `hilbert` reads them. The constant names its Lean
meaning, a definition of `Leanify.Library.MarkovModel`. -/

namespace Leanify.Markov

open UnitSquare Hilbert

def base : Nat := Hilbert.vocab.consts.length

def markovOp : Nat := base

def delta : Vocab where
  consts := [sq ⟶ op1]
  constNames := [w!"T_{#}"]
  constLean := [w!"Leanify.Markov.Model.markovOp"]
  modules := [w!"Leanify.Library.MarkovModel"]
  notions := [
    { name := phrase!"Markov operator of $v$", value := .const markovOp, ty := sq ⟶ op1,
      doms := [some isCopula],
      doc := "`(T_C g)(u) = ∫ g(y) K_C(u, dy)` for a copula `C`, with the conditional distribution `K_C(u,·)` of the second coordinate given the first (Mathlib `Measure.condKernel`): `E[g(V) | U = u]`" }]

/-- `hilbert` (with `unitsquare`) and this field. -/
def vocab : Vocab :=
  let H := Hilbert.vocab
  let D := Vocab.tag w!"markov" delta
  { H with
    consts := H.consts ++ D.consts
    constNames := H.constNames ++ D.constNames
    constLean := H.constLean ++ D.constLean
    modules := H.modules ++ D.modules
    notions := H.notions ++ D.notions }

def withCore : Vocab := Vocab.core ++ vocab

end Leanify.Markov
