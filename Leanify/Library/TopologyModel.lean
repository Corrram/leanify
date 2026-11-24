import Leanify.Denote
import Mathlib.Topology.Perfect
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The meaning of the field `realsets`

Sets of real numbers are predicates; each notion is Mathlib's, of the set `{x | S x}`. -/

namespace Leanify.Topology
open MeasureTheory

abbrev set (S : ℝ → Prop) : Set ℝ := {x | S x}

def Open (S : ℝ → Prop) : Prop := IsOpen (set S)
def Closed (S : ℝ → Prop) : Prop := IsClosed (set S)
def Compact (S : ℝ → Prop) : Prop := IsCompact (set S)
def BoundedAbove (S : ℝ → Prop) : Prop := BddAbove (set S)
def BoundedBelow (S : ℝ → Prop) : Prop := BddBelow (set S)
def Connected (S : ℝ → Prop) : Prop := IsPreconnected (set S)
def IsDense (S : ℝ → Prop) : Prop := Dense (set S)
def NowhereDense (S : ℝ → Prop) : Prop := IsNowhereDense (set S)
def IsPerfect (S : ℝ → Prop) : Prop := Perfect (set S)
def IsFinite (S : ℝ → Prop) : Prop := (set S).Finite
def IsCountable (S : ℝ → Prop) : Prop := (set S).Countable
def Measurable (S : ℝ → Prop) : Prop := NullMeasurableSet (set S) volume
def Null (S : ℝ → Prop) : Prop := volume (set S) = 0
def FiniteMeasure (S : ℝ → Prop) : Prop := volume (set S) ≠ ⊤
def IsConvex (S : ℝ → Prop) : Prop := Convex ℝ (set S)

def closure (S : ℝ → Prop) : ℝ → Prop := fun x => x ∈ _root_.closure (set S)
def interior (S : ℝ → Prop) : ℝ → Prop := fun x => x ∈ _root_.interior (set S)
def boundary (S : ℝ → Prop) : ℝ → Prop := fun x => x ∈ frontier (set S)
def limitPoints (S : ℝ → Prop) : ℝ → Prop := fun x => x ∈ derivedSet (set S)

noncomputable def supremum (S : ℝ → Prop) : ℝ := sSup (set S)
noncomputable def infimum (S : ℝ → Prop) : ℝ := sInf (set S)
noncomputable def diameter (S : ℝ → Prop) : ℝ := Metric.diam (set S)
noncomputable def measure (S : ℝ → Prop) : ℝ := (volume (set S)).toReal
noncomputable def card (S : ℝ → Prop) : ℝ := (set S).ncard
noncomputable def distTo (x : ℝ) (S : ℝ → Prop) : ℝ := Metric.infDist x (set S)
def cantor : ℝ → Prop := fun x => x ∈ cantorSet

end Leanify.Topology
