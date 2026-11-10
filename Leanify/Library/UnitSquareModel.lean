import Leanify.Library.UnitSquare
import Leanify.Denote
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Defs

/-! # The meaning of the unit-square vocabulary

The type `[0,1]` is Mathlib's `↥unitInterval`, with its Lebesgue measure (`volume`) and
the Bochner integral. The meanings of the constants of `UnitSquare.vocab`:

* a function `F` on `[0,1]^2` is a *distribution function on `[0,1]^2`* when it
  is `(u,v) ↦ μ([0,u] × [0,v])` for a probability measure `μ` on `[0,1]^2`;
* it has *uniform marginals* when `F(u,1) = u` and `F(1,v) = v`;
* a set function `γ` on `[0,1]^2` is a *probability measure on `[0,1]^2`* when it
  agrees with a probability measure on measurable sets;
* it has *uniform marginals* when `γ([0,u] × [0,1]) = u` and `γ([0,1] × [0,v]) = v`. -/

namespace Leanify.UnitSquare
open MeasureTheory
open scoped unitInterval

/-- The points of `[0,1]`: Mathlib's `↥unitInterval`. -/
abbrev Interval : Type := I
/-- A point of `[0,1]` (the value of an expression that has none). -/
def Interval.zero : Interval := 0
/-- The number that a point of `[0,1]` is. -/
abbrev Interval.val : I → ℝ := Subtype.val
/-- A number of `[0,1]` as a point of it (the nearest point, for a number outside: the
compiler uses it only for numbers of `[0,1]`). -/
noncomputable abbrev Interval.point : ℝ → I := Set.projIcc 0 1 zero_le_one
/-- The integral over `[0,1]` (the Bochner integral for Lebesgue measure). -/
noncomputable abbrev Interval.integral : (I → ℝ) → ℝ := MeasureTheory.integral MeasureTheory.MeasureSpace.volume
/-- Borel measurable maps of `[0,1]`. -/
abbrev Interval.borel : (I → I) → Prop := fun T => Measurable T

def distFn2 (F : I → I → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ u v : I, F u v = (μ (Set.Iic u ×ˢ Set.Iic v)).toReal

def dfUniformMarginals (F : I → I → ℝ) : Prop :=
  (∀ u : I, F u 1 = u) ∧ ∀ v : I, F 1 v = v

def probMeasure2 (γ : (I → I → Prop) → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ A : I → I → Prop, MeasurableSet {p : I × I | A p.1 p.2} →
      γ A = (μ {p : I × I | A p.1 p.2}).toReal

def measUniformMarginals (γ : (I → I → Prop) → ℝ) : Prop :=
  (∀ u : I, γ (fun x _ => x ≤ u) = u) ∧ ∀ v : I, γ (fun _ z => z ≤ v) = v

end Leanify.UnitSquare

namespace Leanify.Prelude
open MeasureTheory
open scoped unitInterval

/-! Lebesgue measure, measurable sets and integrable functions on `[0,1]`. -/
noncomputable def leb (A : I → Prop) : ℝ := (volume {x : I | A x}).toReal
def measurableSet1 (A : I → Prop) : Prop := MeasurableSet {x : I | A x}
def measurableSet2 (A : I → I → Prop) : Prop := MeasurableSet {p : I × I | A p.1 p.2}
def integrable (f : I → ℝ) : Prop := Integrable f

/-! Quantities of functions on the unit square (of copulas, say), on a class of
them, and classes of such functions. Convexity uses the pointwise vector space
structure; "with respect to uniform convergence" uses the topology of uniform
convergence on `[0,1]²`. -/
/-- A function on the unit square, from the space of uniform convergence on `[0,1]²`. -/
def ofUniform (g : UniformFun (I × I) ℝ) : I → I → ℝ := fun u v => UniformFun.toFun g (u, v)
def convexOnSq (F : (I → I → ℝ) → ℝ) (D : (I → I → ℝ) → Prop) : Prop := ConvexOn ℝ {C | D C} F
def concaveOnSq (F : (I → I → ℝ) → ℝ) (D : (I → I → ℝ) → Prop) : Prop := ConcaveOn ℝ {C | D C} F
def lscUniform (F : (I → I → ℝ) → ℝ) (D : (I → I → ℝ) → Prop) : Prop :=
  LowerSemicontinuousOn (fun g => F (ofUniform g)) {g | D (ofUniform g)}
def uscUniform (F : (I → I → ℝ) → ℝ) (D : (I → I → ℝ) → Prop) : Prop :=
  UpperSemicontinuousOn (fun g => F (ofUniform g)) {g | D (ofUniform g)}
def continuousUniform (F : (I → I → ℝ) → ℝ) (D : (I → I → ℝ) → Prop) : Prop :=
  ContinuousOn (fun g => F (ofUniform g)) {g | D (ofUniform g)}
def convexClass (D : (I → I → ℝ) → Prop) : Prop := Convex ℝ {C | D C}
def compactUniform (D : (I → I → ℝ) → Prop) : Prop :=
  IsCompact {g : UniformFun (I × I) ℝ | D (ofUniform g)}
def closedUniform (D : (I → I → ℝ) → Prop) : Prop :=
  IsClosed {g : UniformFun (I × I) ℝ | D (ofUniform g)}

end Leanify.Prelude

namespace Leanify.UnitSquare

/-- The model of `UnitSquare.vocab`, written out: its type `[0,1]` and its constants.
`#leanify_semantics` builds the same model from the names in the vocabulary
(`Vocab.typeLean`, `Vocab.constLean`), so an article does not have to name it. -/
noncomputable def model : Model where
  base := Model.baseOf [⟨Interval, Interval.zero⟩]
  default := Model.defaultOf [⟨Interval, Interval.zero⟩]
  consts := [⟨sq ⟶ .prop, distFn2⟩, ⟨sq ⟶ .prop, dfUniformMarginals⟩,
    ⟨meas2 ⟶ .prop, probMeasure2⟩, ⟨meas2 ⟶ .prop, measUniformMarginals⟩,
    ⟨Quantity ⟶ Class ⟶ .prop, Prelude.convexOnSq⟩, ⟨Quantity ⟶ Class ⟶ .prop, Prelude.concaveOnSq⟩,
    ⟨Quantity ⟶ Class ⟶ .prop, Prelude.lscUniform⟩, ⟨Quantity ⟶ Class ⟶ .prop, Prelude.uscUniform⟩,
    ⟨Quantity ⟶ Class ⟶ .prop, Prelude.continuousUniform⟩,
    ⟨Class ⟶ .prop, Prelude.convexClass⟩, ⟨Class ⟶ .prop, Prelude.compactUniform⟩,
    ⟨Class ⟶ .prop, Prelude.closedUniform⟩,
    ⟨I01 ⟶ .real, Interval.val⟩, ⟨.real ⟶ I01, Interval.point⟩, ⟨(I01 ⟶ .real) ⟶ .real, Interval.integral⟩,
    ⟨(I01 ⟶ .real) ⟶ .prop, Prelude.integrable⟩, ⟨set1 ⟶ .prop, Prelude.measurableSet1⟩,
    ⟨set2 ⟶ .prop, Prelude.measurableSet2⟩, ⟨set1 ⟶ .real, Prelude.leb⟩, ⟨self ⟶ .prop, Interval.borel⟩]

end Leanify.UnitSquare
