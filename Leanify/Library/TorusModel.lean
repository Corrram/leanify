import Leanify.Library.Torus
import Leanify.Denote
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The meaning of the torus vocabulary

`Torus.model` interprets the four constants of `Torus.vocab` in Mathlib. A function
on `𝕋²` is a function `F : ℝ → ℝ → ℝ`, 1-periodic in each variable. -/

namespace Leanify.Torus
open MeasureTheory

/-- Smooth (`C^∞`) and 1-periodic in each variable. -/
def smoothT2 (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, ContDiff ℝ n (Function.uncurry F)) ∧ ∀ x y, F (x + 1) y = F x y ∧ F x (y + 1) = F x y

/-- Zero mean over a period cell (the Haar mean of `𝕋²`). -/
def zeroMeanT2 (F : ℝ → ℝ → ℝ) : Prop :=
  (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y) = 0

/-- The `C^m` norm: the largest supremum of the norms of the derivatives of order
`k ≤ m` (for real `m`, its integer part). -/
noncomputable def cNormT2 (m : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ⨆ k : Fin (⌊m⌋₊ + 1), ⨆ p : ℝ × ℝ, ‖iteratedFDeriv ℝ (k : ℕ) (Function.uncurry F) p‖

/-- The derivative in the direction `(a, b)`. -/
noncomputable def dirDerivT2 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => fderiv ℝ (Function.uncurry F) (x, y) (a, b)

/-- The model of `Torus.vocab` (no base types). -/
noncomputable def model : Model where
  base := fun _ => Unit
  default := fun _ => ()
  consts := [⟨F2 ⟶ .prop, smoothT2⟩, ⟨F2 ⟶ .prop, zeroMeanT2⟩, ⟨.real ⟶ F2 ⟶ .real, cNormT2⟩,
    ⟨F2 ⟶ .real ⟶ .real ⟶ F2, dirDerivT2⟩]

end Leanify.Torus
