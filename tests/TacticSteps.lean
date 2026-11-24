import Leanify.Library.UnitSquareModel

/-! # The steps of `definedness` and the facts of the unit square

Each example is a leaf of a definedness condition, in the form the compiled statements
have it, and one fact about couplings that the proofs of an article use. -/

open MeasureTheory
open scoped unitInterval
open Leanify.UnitSquare

namespace TacticSteps

/-- Two cases that meet in a point agree there. -/
example (x : ℝ) (h1 : x ≤ 1 / 2) (h2 : 1 / 2 ≤ x) : 1 - 8 * (1 - x) ^ 3 = 8 * x ^ 3 - 1 := by
  leanify_pinch

/-- A strict case or its endpoint, from the weak inequality. -/
example (x : ℝ) : 0 < x ∧ x ≤ 1 / 2 → (0 < x ∧ x < 1 / 2 ∨ x = 1 / 2) := by
  definedness []

/-- A witness that a hypothesis gives. -/
example (a b : ℝ) : ¬a * b = 0 → ∃ y, ¬a * y = 0 := by
  definedness []

/-- A bound of a point of `[0,1]`. -/
example (x : I) : (0 : ℝ) ≤ 1 - x ∧ ¬(2 - (x : ℝ)) = 0 := by
  definedness []

/-- A product that is not zero. -/
example (x : ℝ) : 0 < x ∧ x < 1 → ¬8 * (1 - x) ^ 2 = 0 := by
  definedness []

/-- An integrand given by cases on comparisons is interval integrable. -/
example (w x : ℝ) : Leanify.Prelude.intervalIntegrable
    (fun t => if 0 < t ∧ t < 1 - w then (1 - t) * (2 * t - w) else if 1 - w < t ∧ t < 1 then (t + w - 1) / (2 * w) else 0)
    (1 - w) x := by
  definedness []

/-- A continuous function is integrable, on `[0,1]` and for a coupling. -/
example (f : I → ℝ) (hf : continuousOnInterval f) : Leanify.Prelude.integrable f := by
  definedness []

example (γ : (I → I → Prop) → ℝ) (c : I → I → ℝ) (hγ : probMeasure2 γ ∧ measUniformMarginals γ)
    (hc : continuousOnSquare c) : couplingIntegrable γ fun x z => c x z := by
  definedness []

/-- `Y Z` and `Y F_Y(Y)` are integrable when `Y` is. -/
example (P : (ℝ → I → Prop) → ℝ) (h : jointIntegrable P fun y _ => y) :
    (jointIntegrable P fun y z => y * (z : ℝ)) ∧ jointIntegrable P fun y _ => y * jointDistFn P y := by
  definedness []

/-- A copula and its coupling determine each other. -/
example (C : I → I → ℝ) (h : distFn2 C ∧ dfUniformMarginals C) :
    copulaOfCoupling (couplingOfCopula C) = C :=
  copulaOfCoupling_couplingOfCopula h

/-- The law of `(X, T(X))` for a map `T` that preserves Lebesgue measure is a coupling. -/
example (T : I → I) (hT : lebesguePreserving T) :
    probMeasure2 (fun A => Leanify.Prelude.leb fun x => A x (T x)) ∧
      measUniformMarginals (fun A => Leanify.Prelude.leb fun x => A x (T x)) :=
  ⟨graph_probMeasure2 hT.measurable, graph_measUniformMarginals hT⟩

/-- A limit at a point is the limit along the punctured domain. -/
example : Leanify.Prelude.limAt 0 (fun x => 0 < x ∧ x ≤ 1) (fun x => 2 * x + 1) = 1 := by
  have hS : {x : ℝ | 0 < x ∧ x ≤ 1} \ {0} = Set.Ioc 0 1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_Ioc]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1.ne'⟩⟩
  have : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioc 0 1)) := by
    rw [nhdsWithin_Ioc_eq_nhdsGT (by norm_num)]; infer_instance
  refine Leanify.Prelude.limAt_eq hS ?_
  have hc : Continuous fun x : ℝ => 2 * x + 1 := by fun_prop
  have h := hc.continuousAt (x := 0)
  simpa using h.tendsto.mono_left nhdsWithin_le_nhds

end TacticSteps
