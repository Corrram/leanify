import Leanify.Denote
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The meaning of the field `realfunctions`

The properties of real functions that the core language does not have, as Mathlib's. -/

namespace Leanify.Analysis
open MeasureTheory

def UniformlyContinuous (f : ℝ → ℝ) : Prop := UniformContinuous f
def Smooth (f : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f
def ContinuouslyDifferentiable (f : ℝ → ℝ) : Prop := ContDiff ℝ 1 f
def Analytic (f : ℝ → ℝ) : Prop := AnalyticOnNhd ℝ f Set.univ
def IsMeasurable (f : ℝ → ℝ) : Prop := Measurable f
def IsIntegrable (f : ℝ → ℝ) : Prop := Integrable f volume
def BoundedVariation (a b : ℝ) (f : ℝ → ℝ) : Prop := BoundedVariationOn f (Set.Icc a b)
/-- `|f x - f y| ≤ C |x - y| ^ α` for some `C`. -/
def Holder (α : ℝ) (f : ℝ → ℝ) : Prop := ∃ C : ℝ, ∀ x y, |f x - f y| ≤ C * |x - y| ^ α

noncomputable def derivative (f : ℝ → ℝ) : ℝ → ℝ := deriv f
noncomputable def supNorm (f : ℝ → ℝ) : ℝ := ⨆ x, |f x|
/-- The least Lipschitz constant. -/
noncomputable def lipschitzConstant (f : ℝ → ℝ) : ℝ := sInf {L : ℝ | 0 ≤ L ∧ ∀ x y, |f x - f y| ≤ L * |x - y|}
noncomputable def totalVariation (f : ℝ → ℝ) (a b : ℝ) : ℝ := (eVariationOn f (Set.Icc a b)).toReal
noncomputable def integral (f : ℝ → ℝ) : ℝ := ∫ x, f x
noncomputable def inverse (f : ℝ → ℝ) : ℝ → ℝ := Function.invFun f

/-- Riemann integrable on `[a, b]` (Darboux's criterion; Mathlib has no Riemann integral): `a ≤ b`,
bounded on `[a, b]`, and for every `ε > 0` a partition `a = x₀ ≤ x₁ ≤ ⋯ ≤ xₙ = b` whose upper
and lower sums differ by less than `ε`. -/
def RiemannOn (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  a ≤ b ∧ BddAbove (f '' Set.Icc a b) ∧ BddBelow (f '' Set.Icc a b) ∧
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (x : ℕ → ℝ), x 0 = a ∧ x n = b ∧ (∀ i < n, x i ≤ x (i + 1)) ∧
    ∑ i ∈ Finset.range n, (x (i + 1) - x i) *
      (sSup (f '' Set.Icc (x i) (x (i + 1))) - sInf (f '' Set.Icc (x i) (x (i + 1)))) < ε

/-- Riemann integrable on a domain whose closure is a closed bounded interval `[a, b]`: on
`[a, b]` (the values at the end points do not matter). -/
def RiemannOnSet (D : ℝ → Prop) (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, _root_.closure {x | D x} = Set.Icc a b ∧ RiemannOn a b f

end Leanify.Analysis
