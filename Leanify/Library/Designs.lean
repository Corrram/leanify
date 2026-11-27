import Leanify.Library.Core

/-! # Vocabulary: combinatorial designs

The parameters of balanced incomplete block designs, Steiner triple systems and finite
planes (`We write $r(v,k,\lambda)$ for the replication number of a design with $v$ points,
block size $k$ and index $\lambda$.`).

* modifiers: `admissible for Steiner triple systems` (`v ≡ 1` or `3 (mod 6)`, the orders of
  Steiner triple systems by Kirkman's theorem).
* notions: the replication number and the number of blocks of a 2-`(v,k,λ)` design; the number
  of triples of a Steiner triple system; the numbers of points and lines of a projective plane
  and of an affine plane of order `n`.

The quantities are constants, interpreted by the declarations of
`Leanify/Library/DesignsModel.lean`: their values for every such structure (a design as a
multiset of blocks of `Fin v`; a projective plane as Mathlib's `Configuration.ProjectivePlane`
of that order; an affine plane by its axioms), where there is one, which is part of their
domain. Their formulas (`λ(v-1)/(k-1)`, `λv(v-1)/(k(k-1))`, `v(v-1)/6`, `n² + n + 1`, `n²`,
`n² + n`) are theorems, not definitions. -/

namespace Leanify.Designs
open Build Core

def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def ge2 (n : B) : B := and (isInt n) (le (num 2) n)
def mod6 (v r : B) : B := isInt (div (sub v r) (num 6))
def app3 (f x y z : B) : B := app (app2 f x y) z

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def replication : Nat := 0
def numBlocks : Nat := 1
def numTriples : Nat := 2
def projectivePoints : Nat := 3
def projectiveLines : Nat := 4
def affinePoints : Nat := 5
def affineLines : Nat := 6
def existsDesign : Nat := 7
def existsSTS : Nat := 8
def existsProjective : Nat := 9
def existsAffine : Nat := 10
end Const

/-- A quantity of the 2-`(v,k,λ)` designs, where there is one: the constant `c`. -/
def design (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real ge2, dom2 .real fun v k => and (ge2 k) (lt k v),
      dom3 .real fun v k l => and (posInt l) (app3 (const Const.existsDesign) v k l)], doc, value := .const c }
/-- A quantity of the planes of order `n`, where there is one (the existence constant `e`): the
constant `c`. -/
def plane (name : Phrase) (e c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real fun n => and (ge2 n) (app (const e) n)], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real,
    .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .prop, .real ⟶ .prop, .real ⟶ .prop,
    .real ⟶ .prop]
  constNames := [w!"r_{#1,#2,#3}", w!"b_{#1,#2,#3}", w!"\\operatorname{STS}", w!"\\#\\operatorname{PG}_{#}", w!"\\#\\operatorname{PL}_{#}",
    w!"\\#\\operatorname{AG}_{#}", w!"\\#\\operatorname{AL}_{#}", w!"\\exists D_{#1,#2,#3}", w!"\\exists\\operatorname{STS}_{#}",
    w!"\\exists\\operatorname{PG}_{#}", w!"\\exists\\operatorname{AG}_{#}"]
  constLean := [w!"Leanify.Designs.replication", w!"Leanify.Designs.numBlocks", w!"Leanify.Designs.numTriples",
    w!"Leanify.Designs.projectivePoints", w!"Leanify.Designs.projectiveLines", w!"Leanify.Designs.affinePoints",
    w!"Leanify.Designs.affineLines", w!"Leanify.Designs.ExistsDesign", w!"Leanify.Designs.ExistsSTS",
    w!"Leanify.Designs.ExistsProjectivePlane", w!"Leanify.Designs.ExistsAffinePlane"]
  modules := [w!"Leanify.Library.DesignsModel"]
  mods := [
    { phrase := phrase!"admissible for Steiner triple systems", prenominal := false, ty := .real,
      pred := close <| lamR fun v => and (posInt v) (or (mod6 v (num 1)) (mod6 v (num 3))),
      doc := "a positive integer `v ≡ 1` or `3 (mod 6)`: the orders of Steiner triple systems (Kirkman)" }]
  notions := [
    design phrase!"replication number of a design with $v$ points, block size $v$ and index $v$" Const.replication
      "the blocks through a point of a 2-`(v,k,λ)` design (`λ(v-1)/(k-1)`)",
    design phrase!"number of blocks of a design with $v$ points, block size $v$ and index $v$" Const.numBlocks
      "the blocks of a 2-`(v,k,λ)` design (`λv(v-1)/(k(k-1))`)",
    { name := phrase!"number of triples of a Steiner triple system of order $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun v => and (posInt v) (app (const Const.existsSTS) v)],
      doc := "the blocks of a 2-`(v,3,1)` design, where there is one (`v(v-1)/6`)", value := .const Const.numTriples },
    plane phrase!"number of points of a projective plane of order $v$" Const.existsProjective Const.projectivePoints
      "of Mathlib's `Configuration.ProjectivePlane` of that order, where there is one (`n² + n + 1`)",
    plane phrase!"number of lines of a projective plane of order $v$" Const.existsProjective Const.projectiveLines
      "(`n² + n + 1`)",
    plane phrase!"number of points of an affine plane of order $v$" Const.existsAffine Const.affinePoints "(`n²`)",
    plane phrase!"number of lines of an affine plane of order $v$" Const.existsAffine Const.affineLines "(`n² + n`)"]

end Leanify.Designs
