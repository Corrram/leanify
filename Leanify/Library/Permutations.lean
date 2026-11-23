import Leanify.Library.Core

/-! # Vocabulary: permutations

A permutation is a permutation of `{1, …, n}`, for some `n`, its degree: a type of its own
(Mathlib's `Equiv.Perm (Fin n)`, the point `i` being `i + 1`), so that an article binds
permutations as it binds numbers (`Let $\sigma$ be a permutation of $\{1,\dots,n\}$.`), applies
them to numbers (`\sigma(i)`, for `i` one of `1, …, n`), composes them (`\sigma\tau` is
`σ ∘ τ`, for permutations of the same degree) and takes their powers (`\sigma^k` for a
natural number `k`).

* nouns: `permutation`, `transposition`, `cycle`, `derangement`, `involution`, and `identity`
  (`$\sigma^k$ is the identity`);
* adjectives: `even`, `odd`, `of $\{1,\dots,n\}$`, `of degree $n$`, `on $n$ letters`;
* notions: the sign (also `\operatorname{sgn}\sigma`), the order, the number of fixed
  points, of cycles (fixed points included) and of inversions, the degree, the inverse, the
  identity permutation of `{1, …, n}`, and the set of the permutations of `{1, …, n}`
  (`We write $S_n$ for the set of permutations of $\{1,\dots,n\}$.`).

The constants are interpreted by `Leanify/Library/PermutationsModel.lean`. -/

namespace Leanify.Permutations
open Build Core

/-- Permutations: the field's base type. -/
abbrev P : Ty := .base 0

namespace Const
def degree : Nat := 0
def isPoint : Nat := 1
def apply : Nat := 2
def mul : Nat := 3
def sameDegree : Nat := 4
def pow : Nat := 5
def inverse : Nat := 6
def identity : Nat := 7
def isIdentity : Nat := 8
def sign : Nat := 9
def order : Nat := 10
def numFixed : Nat := 11
def numCycles : Nat := 12
def numInversions : Nat := 13
def isTransposition : Nat := 14
def isCycle : Nat := 15
def isDerangement : Nat := 16
def isInvolution : Nat := 17
end Const
open Const

def pPred (p : B → B) : Tm := close <| lamT P (fun _ => tt) p
def ofP (name : Phrase) (c : Nat) (doc : String) : Notion := { name, value := .const c, ty := P ⟶ .real, doc }
def deg (s : B) : B := app (const degree) s

def nounP (sing plural : Phrase) (pred : Tm) (doc : String) : Noun := { sing, plural, ty := P, pred, doc }
def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := P, pred, doc }

/-- A permutation of `{1, …, n}`. -/
def ofDegree : Tm := close <| lamR fun n => lamT P (fun _ => tt) fun s => eq (deg s) n
def natDom : Option Tm := some nonnegInt

def vocab : Vocab where
  types := [w!"\\mathrm{Perm}"]
  consts := [P ⟶ .real, P ⟶ .real ⟶ .prop, P ⟶ .real ⟶ .real, P ⟶ P ⟶ P, P ⟶ P ⟶ .prop, P ⟶ .real ⟶ P,
    P ⟶ P, .real ⟶ P, P ⟶ .prop, P ⟶ .real, P ⟶ .real, P ⟶ .real, P ⟶ .real, P ⟶ .real,
    P ⟶ .prop, P ⟶ .prop, P ⟶ .prop, P ⟶ .prop]
  constNames := [w!"\\deg", w!"#2\\in\\{1,\\dots,\\deg #1\\}", w!"", w!"\\cdot", w!"\\deg #1=\\deg #2", w!"^",
    w!"#^{-1}", w!"\\operatorname{id}_{#}", w!"\\operatorname{IsId}", w!"\\operatorname{sgn}",
    w!"\\operatorname{ord}", w!"\\operatorname{fix}", w!"\\operatorname{cyc}", w!"\\operatorname{inv}",
    w!"\\operatorname{Transposition}", w!"\\operatorname{Cycle}", w!"\\operatorname{Derangement}",
    w!"\\operatorname{Involution}"]
  constLean := [w!"Leanify.Permutations.degree", w!"Leanify.Permutations.IsPoint", w!"Leanify.Permutations.apply",
    w!"Leanify.Permutations.mul", w!"Leanify.Permutations.SameDegree", w!"Leanify.Permutations.pow",
    w!"Leanify.Permutations.inverse", w!"Leanify.Permutations.identity", w!"Leanify.Permutations.IsIdentity",
    w!"Leanify.Permutations.sign", w!"Leanify.Permutations.order", w!"Leanify.Permutations.numFixed",
    w!"Leanify.Permutations.numCycles", w!"Leanify.Permutations.numInversions",
    w!"Leanify.Permutations.IsTransposition", w!"Leanify.Permutations.IsCycle",
    w!"Leanify.Permutations.IsDerangement", w!"Leanify.Permutations.IsInvolution"]
  typeLean := [(w!"Leanify.Permutations.Perm", w!"Leanify.Permutations.Perm.empty")]
  modules := [w!"Leanify.Library.PermutationsModel"]
  nouns := [
    nounP phrase!"permutation" phrase!"permutations" (pPred fun _ => tt)
      "a permutation of `{1, …, n}` for some `n` (Mathlib `Equiv.Perm (Fin n)`)",
    nounP phrase!"transposition" phrase!"transpositions" (.const isTransposition)
      "exchanges two points (Mathlib `Equiv.Perm.IsSwap`)",
    nounP phrase!"cycle" phrase!"cycles" (.const isCycle) "a single nontrivial cycle (Mathlib `Equiv.Perm.IsCycle`)",
    nounP phrase!"derangement" phrase!"derangements" (.const isDerangement) "without fixed points",
    nounP phrase!"involution" phrase!"involutions" (.const isInvolution) "`σ² = id`",
    nounP phrase!"identity" phrase!"identities" (.const isIdentity) "the identity permutation (of its degree)",
    nounP phrase!"identity permutation" phrase!"identity permutations" (.const isIdentity)
      "the identity permutation (of its degree)"]
  mods := [
    mod phrase!"even" true (pPred fun s => eq (app (const sign) s) (num 1)) "sign `1` (Mathlib `Equiv.Perm.sign`)",
    mod phrase!"odd" true (pPred fun s => eq (app (const sign) s) (neg (num 1))) "sign `-1` (Mathlib `Equiv.Perm.sign`)",
    mod phrase!"of $\\{1,\\dots,v\\}$" false ofDegree "of degree `n`",
    mod phrase!"of $\\{1,\\ldots,v\\}$" false ofDegree "of degree `n`",
    mod phrase!"of degree $v$" false ofDegree "a permutation of `{1, …, n}`",
    mod phrase!"on $v$ letters" false ofDegree "a permutation of `{1, …, n}`"]
  notions := [
    ofP phrase!"sign of $v$" sign "`1` or `-1` (Mathlib `Equiv.Perm.sign`)",
    ofP phrase!"signature of $v$" sign "`1` or `-1` (Mathlib `Equiv.Perm.sign`)",
    ofP phrase!"order of $v$" order "the least `k ≥ 1` with `σ^k = id` (Mathlib `orderOf`)",
    ofP phrase!"number of fixed points of $v$" numFixed "the `i` with `σ(i) = i`",
    ofP phrase!"number of cycles of $v$" numCycles "in its cycle decomposition, fixed points included (Mathlib `Equiv.Perm.cycleType`)",
    ofP phrase!"number of inversions of $v$" numInversions "the pairs `i < j` with `σ(i) > σ(j)`",
    ofP phrase!"degree of $v$" degree "`n`, for a permutation of `{1, …, n}`",
    { name := phrase!"inverse of $v$", value := .const inverse, ty := P ⟶ P, doc := "`σ⁻¹`" },
    { name := phrase!"identity permutation of $\\{1,\\dots,v\\}$", value := .const identity, ty := .real ⟶ P,
      doms := [natDom], doc := "`id`, of degree `n`" },
    { name := phrase!"identity permutation of $\\{1,\\ldots,v\\}$", value := .const identity, ty := .real ⟶ P,
      doms := [natDom], doc := "`id`, of degree `n`" },
    { name := phrase!"set of permutations of $\\{1,\\dots,v\\}$", value := ofDegree, ty := .real ⟶ P ⟶ .prop,
      doms := [natDom], doc := "the symmetric group `S_n`" },
    { name := phrase!"set of permutations of $\\{1,\\ldots,v\\}$", value := ofDegree, ty := .real ⟶ P ⟶ .prop,
      doms := [natDom], doc := "the symmetric group `S_n`" },
    { name := phrase!"symmetric group on $v$ letters", value := ofDegree, ty := .real ⟶ P ⟶ .prop,
      doms := [natDom], doc := "the permutations of `{1, …, n}`" }]
  methods := [
    { ty := P, op := .call, const := apply, doc := "`σ(i)`, for `i` one of `1, …, n`",
      dom := some (close <| lamT P (fun _ => tt) fun s => lamR fun i => app2 (const isPoint) s i) },
    { ty := P, op := .mul, const := mul, doc := "`στ = σ ∘ τ`, for permutations of the same degree",
      dom := some (.const sameDegree) },
    { ty := P, op := .pow, const := pow, doc := "`σ^k`, for a natural number `k`" },
    { ty := P, op := .fn w!"sgn", const := sign, doc := "the sign (Mathlib `Equiv.Perm.sign`)" },
    { ty := P, op := .fn w!"sign", const := sign, doc := "the sign (Mathlib `Equiv.Perm.sign`)" }]

end Leanify.Permutations
