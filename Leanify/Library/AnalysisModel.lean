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

end Leanify.Analysis
