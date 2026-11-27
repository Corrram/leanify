import Leanify.Library.Core

/-! # Vocabulary: sets of real numbers (the field `realsets`)

The topology and measure of the real line. A set is a set of real numbers (a predicate of
real numbers, as everywhere in Leanify), so that an article binds sets by a noun (`Let $S$
be a nonempty compact set.`, `every open subset $U$ of $\mathbb{R}$`) and writes `x\in S`.

* nouns: `set`, `set of real numbers`, `set of natural numbers`, `set of integers`, `set of
  positive integers`, `subset of $\mathbb{R}$`, `null set`, `interval` (`open
  interval`, `closed bounded interval`, … with the adjectives);
* adjectives: `open`, `closed`, `compact`, `bounded`, `bounded above`, `bounded below`,
  `connected`, `dense`, `nowhere dense`, `perfect`, `discrete`, `finite`, `infinite`,
  `countable`, `uncountable`, `nonempty`, `empty`, `convex`, `measurable`,
  `of measure zero`, `dense in $B$`, `with a least element` (`$S$ has a least element`), `with a
  greatest element`;
* notions: the closure, interior, boundary and complement of a set, its limit points and
  isolated points, its supremum, infimum and diameter, its Lebesgue measure, its number
  of elements, the distance from a point to a set, and the Cantor set.

The supremum is defined for a nonempty set that is bounded above (the infimum: below), the
diameter for a nonempty bounded set, the Lebesgue measure for a measurable set of finite
measure, the number of elements for a finite set. The constants are interpreted by
`Leanify/Library/TopologyModel.lean`, through Mathlib's topology and measure on `ℝ`. -/

namespace Leanify.Topology
open Build Core

/-- Sets of real numbers. -/
abbrev S : Ty := .real ⟶ .prop

/-- The constants, in the order of their indices: `(type, TeX name, Lean name)`. -/
def table : List (Ty × Codes × Codes) := [
  (S ⟶ .prop, w!"\\operatorname{Open}", w!"Leanify.Topology.Open"),               -- 0
  (S ⟶ .prop, w!"\\operatorname{Closed}", w!"Leanify.Topology.Closed"),           -- 1
  (S ⟶ .prop, w!"\\operatorname{Compact}", w!"Leanify.Topology.Compact"),         -- 2
  (S ⟶ .prop, w!"\\operatorname{BddAbove}", w!"Leanify.Topology.BoundedAbove"),   -- 3
  (S ⟶ .prop, w!"\\operatorname{BddBelow}", w!"Leanify.Topology.BoundedBelow"),   -- 4
  (S ⟶ .prop, w!"\\operatorname{Connected}", w!"Leanify.Topology.Connected"),     -- 5
  (S ⟶ .prop, w!"\\operatorname{Dense}", w!"Leanify.Topology.IsDense"),           -- 6
  (S ⟶ .prop, w!"\\operatorname{NowhereDense}", w!"Leanify.Topology.NowhereDense"), -- 7
  (S ⟶ .prop, w!"\\operatorname{Perfect}", w!"Leanify.Topology.IsPerfect"),       -- 8
  (S ⟶ .prop, w!"\\operatorname{Finite}", w!"Leanify.Topology.IsFinite"),         -- 9
  (S ⟶ .prop, w!"\\operatorname{Countable}", w!"Leanify.Topology.IsCountable"),   -- 10
  (S ⟶ .prop, w!"\\operatorname{Measurable}", w!"Leanify.Topology.Measurable"),   -- 11
  (S ⟶ .prop, w!"\\operatorname{Null}", w!"Leanify.Topology.Null"),               -- 12
  (S ⟶ .prop, w!"\\operatorname{FiniteMeasure}", w!"Leanify.Topology.FiniteMeasure"), -- 13
  (S ⟶ S, w!"\\operatorname{cl}", w!"Leanify.Topology.closure"),                        -- 14
  (S ⟶ S, w!"\\operatorname{int}", w!"Leanify.Topology.interior"),                -- 15
  (S ⟶ S, w!"\\partial", w!"Leanify.Topology.boundary"),                           -- 16
  (S ⟶ S, w!"\\operatorname{acc}", w!"Leanify.Topology.limitPoints"),             -- 17
  (S ⟶ .real, w!"\\sup", w!"Leanify.Topology.supremum"),                           -- 18
  (S ⟶ .real, w!"\\inf", w!"Leanify.Topology.infimum"),                            -- 19
  (S ⟶ .real, w!"\\operatorname{diam}", w!"Leanify.Topology.diameter"),           -- 20
  (S ⟶ .real, w!"\\lambda", w!"Leanify.Topology.measure"),                         -- 21
  (S ⟶ .real, w!"\\#", w!"Leanify.Topology.card"),                                 -- 22
  (.real ⟶ S ⟶ .real, w!"\\operatorname{dist}", w!"Leanify.Topology.distTo"),     -- 23
  (S, w!"\\mathcal{C}", w!"Leanify.Topology.cantor"),                              -- 24
  (S ⟶ .prop, w!"\\operatorname{Convex}", w!"Leanify.Topology.IsConvex")]         -- 25

def sPred (p : B → B) : Tm := close <| lamT S (fun _ => tt) p
def c1 (i : Nat) (s : B) : B := app (const i) s
def nonempty (s : B) : B := exR fun x => app s x
def bounded (s : B) : B := and (c1 3 s) (c1 4 s)

def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := S, pred, doc }
def nounS (sing plural : Phrase) (pred : Tm) (doc : String) : Noun := { sing, plural, ty := S, pred, doc }
def ofS (name : Phrase) (value : Tm) (ty : Ty) (dom : Option Tm) (doc : String) : Notion :=
  { name, value, ty, doms := [dom], doc }

def anySet : Tm := sPred fun _ => tt

def vocab : Vocab where
  consts := table.map (·.1)
  constNames := table.map (·.2.1)
  constLean := table.map (·.2.2)
  modules := [w!"Leanify.Library.TopologyModel"]
  nouns := [
    nounS phrase!"set" phrase!"sets" anySet "a set of real numbers (Mathlib `Set ℝ`)",
    nounS phrase!"set of real numbers" phrase!"sets of real numbers" anySet "(Mathlib `Set ℝ`)",
    nounS phrase!"subset $v$ of $\\mathbb{R}$" phrase!"subsets $v$ of $\\mathbb{R}$" anySet "(Mathlib `Set ℝ`)",
    nounS phrase!"set of natural numbers" phrase!"sets of natural numbers" (sPred fun s => allR fun x => imp (app s x) (isNat x))
      "a subset of `ℕ = {0, 1, 2, …}` (Mathlib `Set ℕ`)",
    nounS phrase!"set of positive integers" phrase!"sets of positive integers"
      (sPred fun s => allR fun x => imp (app s x) (and (isInt x) (lt (num 0) x))) "a subset of `{1, 2, …}`",
    nounS phrase!"set of integers" phrase!"sets of integers" (sPred fun s => allR fun x => imp (app s x) (isInt x))
      "a subset of `ℤ` (Mathlib `Set ℤ`)",
    nounS phrase!"null set" phrase!"null sets" (.const 12) "of Lebesgue measure zero",
    nounS phrase!"interval" phrase!"intervals" (.const 25)
      "every number between two of its numbers is in it (Mathlib `Set.OrdConnected`, `Convex ℝ`): possibly empty, a point or unbounded",
    { nounS phrase!"subset" phrase!"subsets" anySet "a set of real numbers inside another" with
      arg := some ([w!"of"], .real ⟶ .prop, close <| lamT (.real ⟶ .prop) (fun _ => tt) fun a => lamT (.real ⟶ .prop) (fun _ => tt) fun b =>
        allR fun x => imp (app b x) (app a x)) },
    { sing := phrase!"element", plural := phrase!"elements", ty := .real, pred := predR fun _ => tt,
      arg := some ([w!"of"], .real ⟶ .prop, close <| lamT (.real ⟶ .prop) (fun _ => tt) fun a => lamR fun x => app a x),
      doc := "a number in a set of real numbers" },
    { sing := phrase!"upper bound", plural := phrase!"upper bounds", ty := .real, pred := predR fun _ => tt,
      arg := some ([w!"of", w!"for"], .real ⟶ .prop, close <| lamT (.real ⟶ .prop) (fun _ => tt) fun a => lamR fun u =>
        allR fun x => imp (app a x) (le x u)),
      doc := "a number `u` with `a ≤ u` for every `a` of the set (Mathlib `upperBounds`)" },
    { sing := phrase!"lower bound", plural := phrase!"lower bounds", ty := .real, pred := predR fun _ => tt,
      arg := some ([w!"of", w!"for"], .real ⟶ .prop, close <| lamT (.real ⟶ .prop) (fun _ => tt) fun a => lamR fun l =>
        allR fun x => imp (app a x) (le l x)),
      doc := "a number `l` with `l ≤ a` for every `a` of the set (Mathlib `lowerBounds`)" }]
  mods := [
    mod phrase!"open" true (.const 0) "(Mathlib `IsOpen`)",
    mod phrase!"closed" true (.const 1) "(Mathlib `IsClosed`)",
    mod phrase!"compact" true (.const 2) "(Mathlib `IsCompact`)",
    mod phrase!"bounded" true (sPred fun s => bounded s) "bounded above and below (Mathlib `Bornology.IsBounded`)",
    mod phrase!"bounded above" true (.const 3) "(Mathlib `BddAbove`)",
    mod phrase!"bounded below" true (.const 4) "(Mathlib `BddBelow`)",
    mod phrase!"connected" true (.const 5) "an interval, possibly empty (Mathlib `IsPreconnected`)",
    mod phrase!"dense" true (.const 6) "(Mathlib `Dense`)",
    mod phrase!"dense in $v$" false (close <| lamT S (fun _ => tt) fun b => lamT S (fun _ => tt) fun a =>
        and (allR fun x => imp (app a x) (app b x)) (allR fun x => imp (app b x) (app (app (const 14) a) x)))
      "a subset of `B` whose closure contains `B` (`\\mathbb{Q}` is dense in `\\mathbb{R}`; Mathlib `Dense` in the subspace)",
    mod phrase!"nowhere dense" true (.const 7) "the closure has empty interior (Mathlib `IsNowhereDense`)",
    mod phrase!"perfect" true (.const 8) "closed, without isolated points (Mathlib `Perfect`)",
    mod phrase!"discrete" true (sPred fun s => allR fun x => imp (app s x) (not (app (app (const 17) s) x)))
      "every point is isolated",
    mod phrase!"finite" true (.const 9) "(Mathlib `Set.Finite`)",
    mod phrase!"with $v$ elements" false (close <| lamR fun n => lamT S (fun _ => tt) fun a => app2 (prim .cardIs) a n)
      "finite, with `n` elements (Mathlib `Set.ncard`)",
    mod phrase!"infinite" true (sPred fun s => not (c1 9 s)) "(Mathlib `Set.Infinite`)",
    mod phrase!"countable" true (.const 10) "finite or countably infinite (Mathlib `Set.Countable`)",
    mod phrase!"uncountable" true (sPred fun s => not (c1 10 s)) "not countable",
    mod phrase!"nonempty" true (sPred fun s => nonempty s) "(Mathlib `Set.Nonempty`)",
    mod phrase!"empty" true (sPred fun s => not (nonempty s)) "`∅`",
    mod phrase!"with a least element" false (sPred fun s => exR fun m => and (app s m) (allR fun x => imp (app s x) (le m x)))
      "an element at most every element (Mathlib `IsLeast`; `$S$ has a least element`)",
    mod phrase!"with a smallest element" false (sPred fun s => exR fun m => and (app s m) (allR fun x => imp (app s x) (le m x)))
      "(Mathlib `IsLeast`)",
    mod phrase!"with a greatest element" false (sPred fun s => exR fun m => and (app s m) (allR fun x => imp (app s x) (le x m)))
      "an element at least every element (Mathlib `IsGreatest`; `$S$ has a greatest element`)",
    mod phrase!"with a largest element" false (sPred fun s => exR fun m => and (app s m) (allR fun x => imp (app s x) (le x m)))
      "(Mathlib `IsGreatest`)",
    mod phrase!"convex" true (.const 25) "an interval (Mathlib `Convex ℝ`)",
    mod phrase!"measurable" true (.const 11) "Lebesgue measurable (Mathlib `NullMeasurableSet`)",
    mod phrase!"null" true (.const 12) "of Lebesgue measure zero",
    mod phrase!"of measure zero" false (.const 12) "Lebesgue measure zero",
    mod phrase!"of Lebesgue measure zero" false (.const 12) "(Mathlib `MeasureTheory.volume`)",
    mod phrase!"with Lebesgue measure zero" false (.const 12) "(`$S$ has Lebesgue measure zero`)",
    mod phrase!"with measure zero" false (.const 12) "(`$S$ has measure zero`)",
    mod phrase!"of finite measure" false (sPred fun s => and (c1 11 s) (c1 13 s)) "measurable, of finite Lebesgue measure"]
  notions := [
    ofS phrase!"closure of $v$" (.const 14) (S ⟶ S) none "(Mathlib `closure`)",
    ofS phrase!"interior of $v$" (.const 15) (S ⟶ S) none "(Mathlib `interior`)",
    ofS phrase!"boundary of $v$" (.const 16) (S ⟶ S) none "(Mathlib `frontier`)",
    ofS phrase!"complement of $v$" (close <| lamT S (fun _ => tt) fun s => lamR fun x => not (app s x)) (S ⟶ S) none
      "`ℝ ∖ S`",
    ofS phrase!"set of limit points of $v$" (.const 17) (S ⟶ S) none "the accumulation points (Mathlib `derivedSet`)",
    ofS phrase!"set of accumulation points of $v$" (.const 17) (S ⟶ S) none "(Mathlib `derivedSet`)",
    ofS phrase!"set of isolated points of $v$"
      (close <| lamT S (fun _ => tt) fun s => lamR fun x => and (app s x) (not (app (app (const 17) s) x))) (S ⟶ S) none
      "the points of `S` that are not limit points of `S`",
    ofS phrase!"supremum of $v$" (.const 18) (S ⟶ .real) (some (sPred fun s => and (nonempty s) (c1 3 s)))
      "of a nonempty set that is bounded above (Mathlib `sSup`)",
    ofS phrase!"infimum of $v$" (.const 19) (S ⟶ .real) (some (sPred fun s => and (nonempty s) (c1 4 s)))
      "of a nonempty set that is bounded below (Mathlib `sInf`)",
    ofS phrase!"diameter of $v$" (.const 20) (S ⟶ .real) (some (sPred fun s => and (nonempty s) (bounded s)))
      "of a nonempty bounded set (Mathlib `Metric.diam`)",
    ofS phrase!"Lebesgue measure of $v$" (.const 21) (S ⟶ .real) (some (sPred fun s => and (c1 11 s) (c1 13 s)))
      "of a measurable set of finite measure (Mathlib `MeasureTheory.volume`)",
    ofS phrase!"measure of $v$" (.const 21) (S ⟶ .real) (some (sPred fun s => and (c1 11 s) (c1 13 s)))
      "the Lebesgue measure, of a measurable set of finite measure",
    ofS phrase!"number of elements of $v$" (.const 22) (S ⟶ .real) (some (.const 9))
      "of a finite set (Mathlib `Set.ncard`)",
    ofS phrase!"cardinality of $v$" (.const 22) (S ⟶ .real) (some (.const 9)) "of a finite set (Mathlib `Set.ncard`)",
    { name := phrase!"distance from $v$ to $v$", value := .const 23, ty := .real ⟶ S ⟶ .real,
      doms := [none, some (sPred fun s => nonempty s)], doc := "`inf {|x - y| : y ∈ S}`, for a nonempty set (Mathlib `Metric.infDist`)" },
    { name := phrase!"Cantor set", value := .const 24, ty := S, doc := "the middle-thirds Cantor set (Mathlib `cantorSet`)" },
    { name := phrase!"set of rational numbers", value := close (lamR fun x => app (lift Core.rational) x), ty := S,
      doc := "`ℚ ⊆ ℝ`" },
    { name := phrase!"set of irrational numbers", value := close (lamR fun x => not (app (lift Core.rational) x)), ty := S,
      doc := "`ℝ ∖ ℚ`" },
    { name := phrase!"set of integers", value := close (lamR fun x => isInt x), ty := S, doc := "`ℤ ⊆ ℝ`" }]

end Leanify.Topology
