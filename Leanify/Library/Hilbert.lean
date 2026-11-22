import Leanify.Library.UnitSquare
import Leanify.Library.Build

/-! # Vocabulary: square-integrable functions and operators on them

The field `hilbert` extends `unitsquare` with the Hilbert space of square-integrable
functions on `[0,1]` and the operators on it:

* `L^2` and `L^2_0` (the functions with integral zero), as classes of functions of `[0,1]`;
* the inner product `\langle f,g\rangle` and the norm `\lVert f\rVert` of such functions, and of
  kernels (square-integrable functions of the terms of a sequence in `[0,1]`, for independent
  uniform terms);
* an operator `T` (a map of functions of `[0,1]` to such functions) applied to a function by
  juxtaposition, `Tg` and `(Tg)(u)`, its norm on a class of functions, `\lVert T|_{A}\rVert`, and
  its tensor power `T^{\otimes m}`, which applies `T` to each of the terms `1, …, m` of a
  sequence: an operator on kernels;
* the components `F_S` of a kernel `F` in its Hoeffding decomposition, for finite sets `S` of
  positive integers, and the subspace of the components for `S`;
* the phrases `fixes the constants`, `maps $A$ into itself [with norm $r$]`, `is $c$ times the
  identity on $A$`, and `depends only on the first $m$ terms`.

An operator's statements are about its values as elements of `L^2`: two functions that agree
almost everywhere are the same element, so `T is c times the identity on A` says that
`\lVert Tg-cg\rVert = 0` for every `g` in `A`. Each constant names its Lean meaning, a definition
of `Leanify.Library.HilbertModel`. -/

namespace Leanify.Hilbert

open UnitSquare

/-- Real functions on `[0,1]`, operators on them, kernels, and operators on kernels. -/
abbrev fn1 : Ty := I01 ⟶ .real
abbrev op1 : Ty := fn1 ⟶ fn1
abbrev kern : Ty := seq ⟶ .real
abbrev opK : Ty := kern ⟶ kern
/-- Sets of real numbers (finite sets of positive integers, the index sets `S`). -/
abbrev rset : Ty := .real ⟶ .prop

/-- The first constant of this field: its constants follow those of `unitsquare`. -/
def base : Nat := UnitSquare.vocab.consts.length

def memL2 : Nat := base
def memL20 : Nat := base + 1
def inner1 : Nat := base + 2
def norm1 : Nat := base + 3
def innerSeq : Nat := base + 4
def normSeq : Nat := base + 5
def opNorm1 : Nat := base + 6
def opNormSeq : Nat := base + 7
def tensor : Nat := base + 8
def hoeff : Nat := base + 9
def hspace : Nat := base + 10
def dependsFirst : Nat := base + 11
def subsetSum : Nat := base + 12

/-- The constants of this field, in order: their types, readable names, and Lean meanings. -/
def consts : List Ty := [fn1 ⟶ .prop, fn1 ⟶ .prop, fn1 ⟶ fn1 ⟶ .real, fn1 ⟶ .real,
  kern ⟶ kern ⟶ .real, kern ⟶ .real, op1 ⟶ (fn1 ⟶ .prop) ⟶ .real, opK ⟶ (kern ⟶ .prop) ⟶ .real,
  op1 ⟶ .real ⟶ opK, kern ⟶ rset ⟶ kern, rset ⟶ kern ⟶ .prop, kern ⟶ .real ⟶ .prop,
  .real ⟶ (rset ⟶ .real) ⟶ .real]

def constNames : List Codes := [w!"L^2", w!"L^2_0", w!"\\langle #1,#2\\rangle", w!"\\lVert #\\rVert",
  w!"\\langle #1,#2\\rangle", w!"\\lVert #\\rVert", w!"\\lVert #1|_{#2}\\rVert", w!"\\lVert #1|_{#2}\\rVert",
  w!"{#1}^{\\otimes #2}", w!"{#1}_{#2}", w!"H_{#}", w!"\\operatorname{dep}(#1,#2)",
  w!"\\sum_{S\\subseteq\\{1,\\dots,#1\\}}#2"]

def constLean : List Codes := [w!"Leanify.Hilbert.memL2", w!"Leanify.Hilbert.memL20",
  w!"Leanify.Hilbert.inner1", w!"Leanify.Hilbert.norm1", w!"Leanify.Hilbert.innerSeq",
  w!"Leanify.Hilbert.normSeq", w!"Leanify.Hilbert.opNormOn", w!"Leanify.Hilbert.opNormOnSeq",
  w!"Leanify.Hilbert.tensorPow", w!"Leanify.Hilbert.hoeffding", w!"Leanify.Hilbert.hoeffSpace",
  w!"Leanify.Hilbert.dependsFirst", w!"Leanify.Hilbert.subsetSum"]

/-- A finite set of positive integers. -/
def finPos : Tm := Build.close (Build.lamT rset (fun _ => Build.tt) fun S =>
  Build.and (Build.exR fun r => Build.app2 (Build.prim .cardIs) S r)
    (Build.allR fun x => Build.imp (Build.app S x) (Build.and (Build.isInt x) (Build.le (Build.num 1) x))))

/-- The entries of this field (without those of `unitsquare`), with the constant indices
that follow `unitsquare`'s. -/
def delta : Vocab where
  consts := consts
  constNames := constNames
  constLean := constLean
  modules := [w!"Leanify.Library.HilbertModel"]
  nouns := [
    { sing := phrase!"finite set of positive integers", plural := phrase!"finite sets of positive integers",
      ty := rset, pred := finPos,
      doc := "a finite set of integers `≥ 1` (an index set of the terms of a sequence)" }]
  symbols := [
    { sym := w!"L^2", ty := fn1 ⟶ .prop, const := some memL2,
      doc := "the square-integrable functions on `[0,1]`: measurable, with an integrable square (Mathlib `MemLp f 2`)" },
    { sym := w!"L^2_0", ty := fn1 ⟶ .prop, const := some memL20,
      doc := "the functions of `L^2` with integral zero" }]

/-- `unitsquare` with this field. -/
def vocab : Vocab :=
  let U := Vocab.tag w!"unitsquare" UnitSquare.vocab
  let D := Vocab.tag w!"hilbert" delta
  { U with
    consts := U.consts ++ D.consts
    constNames := U.constNames ++ D.constNames
    constLean := U.constLean ++ D.constLean
    modules := U.modules ++ D.modules
    nouns := U.nouns ++ D.nouns
    symbols := U.symbols ++ D.symbols
    intervals := U.intervals.map fun iv =>
      { iv with memL2 := some memL2, memL20 := some memL20, inner1 := some inner1, norm1 := some norm1,
                innerSeq := some innerSeq, normSeq := some normSeq, opNorm1 := some opNorm1,
                opNormSeq := some opNormSeq, tensor := some tensor, hoeff := some hoeff,
                hspace := some hspace, dependsFirst := some dependsFirst,
                isKernel := some UnitSquare.kernel, subsetSum := some subsetSum } }

def withCore : Vocab := Vocab.core ++ vocab

end Leanify.Hilbert
