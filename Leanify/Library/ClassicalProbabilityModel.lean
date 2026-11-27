import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Perm
import Leanify.Denote

/-! # The meaning of the field `classicalprobability`

The classical problems as probabilities and expectations in their probability spaces: the
uniform distribution on a finite set of outcomes (the birthdays `Fin n → Fin d`, the orders of
the votes, the permutations, the sequences of tosses: the number of favourable outcomes over the
number of outcomes), the infinite sequence of independent uniform draws for the coupons (Mathlib
`Measure.infinitePi`), and the uniform position and angle of Buffon's needle (Lebesgue measure).
The closed forms (`1 - d!/((d-n)! d^n)`, `n H_n`, `(a-b)/(a+b)`, `∑ (-1)^k/k!`, `2ℓ/(π d)`,
`(r/n) ∑ 1/(k-1)`, `(n+1)/4`) are theorems, not definitions; the optimal cutoff of the secretary
problem is the least cutoff with the greatest success probability. -/

namespace Leanify.ClassicalProbability

noncomputable section
open MeasureTheory

/-- The probability of a shared birthday among `n` people with `d` equally likely days: of the
birthday assignments `Fin n → Fin d` that are not injective. -/
def birthday (n d : ℝ) : ℝ :=
  (Nat.card {f : Fin ⌊n⌋₊ → Fin ⌊d⌋₊ // ¬ Function.Injective f} : ℝ) / (Nat.card (Fin ⌊n⌋₊ → Fin ⌊d⌋₊) : ℝ)

/-- The sequences of independent uniform draws of `n` coupons. -/
def couponMeasure (n : ℕ) : Measure (ℕ → Fin n) :=
  Measure.infinitePi fun _ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin n))

/-- The number of draws until every coupon has been drawn (`⊤` if one never is). -/
def drawsToCollect {n : ℕ} (ω : ℕ → Fin n) : ℕ∞ := ⨅ (t : ℕ) (_ : ∀ c, ∃ k < t, ω k = c), (t : ℕ∞)

/-- The expected number of draws to collect `n` coupons. -/
def coupons (n : ℝ) : ℝ := (∫⁻ ω, (drawsToCollect ω : ENNReal) ∂(couponMeasure ⌊n⌋₊)).toReal

/-- The orders of the count of `a` votes for the winner (`true`) and `b` for the loser. -/
def counts (a b : ℕ) : Type := {s : Fin (a + b) → Bool // (Finset.univ.filter fun i => s i = true).card = a}

/-- The winner is strictly ahead throughout the count: after each of the first `t ≥ 1` votes. -/
def AheadThroughout {a b : ℕ} (s : counts a b) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ a + b →
    (Finset.univ.filter fun i : Fin (a + b) => (i : ℕ) < t ∧ s.1 i = false).card <
      (Finset.univ.filter fun i : Fin (a + b) => (i : ℕ) < t ∧ s.1 i = true).card

/-- The ballot probability for `a` and `b` votes: that the winner is ahead throughout a uniformly
random order of the count. -/
def ballot (a b : ℝ) : ℝ :=
  (Nat.card {s : counts ⌊a⌋₊ ⌊b⌋₊ // AheadThroughout s} : ℝ) / (Nat.card (counts ⌊a⌋₊ ⌊b⌋₊) : ℝ)

/-- The probability of a derangement of `n` elements: of a uniformly random permutation without a
fixed point (Mathlib `derangements`). -/
def derangementProb (n : ℝ) : ℝ :=
  (Nat.card (derangements (Fin ⌊n⌋₊)) : ℝ) / (Nat.card (Equiv.Perm (Fin ⌊n⌋₊)) : ℝ)

/-- The probability that Buffon's needle of length `ℓ` crosses a line of a grid with spacing `d`:
the distance `x ∈ [0, d/2]` of its centre to the nearest line and its angle `θ ∈ [0, π/2]` with
the lines uniform and independent, it crosses when `x ≤ (ℓ/2) sin θ`. -/
def buffon (ℓ d : ℝ) : ℝ :=
  (volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ d / 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2 ∧ p.1 ≤ ℓ / 2 * Real.sin p.2}).toReal /
    (d / 2 * (Real.pi / 2))

/-- The strategy with cutoff `r` succeeds on the candidates ranked by `σ` (the larger the better):
it rejects the first `r` and takes the first later one better than all before it, and that one
is the best. -/
def SecretarySuccess {n : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i : Fin n, r ≤ (i : ℕ) ∧ (∀ k, σ k ≤ σ i) ∧
    ∀ j : Fin n, r ≤ (j : ℕ) → j < i → ∃ k < j, σ j < σ k

/-- The success probability of the secretary problem with `n` candidates and cutoff `r`: over a
uniformly random order of the candidates. -/
def successNat (n r : ℕ) : ℝ :=
  (Nat.card {σ : Equiv.Perm (Fin n) // SecretarySuccess r σ} : ℝ) / (Nat.card (Equiv.Perm (Fin n)) : ℝ)

def success (n r : ℝ) : ℝ := successNat ⌊n⌋₊ ⌊r⌋₊

/-- The optimal cutoff of the secretary problem with `n` candidates: the least cutoff `r < n` with
the greatest success probability. -/
def optimalCutoff (n : ℝ) : ℝ := by
  classical exact
  if h : ∃ r : ℕ, r < ⌊n⌋₊ ∧ ∀ s < ⌊n⌋₊, successNat ⌊n⌋₊ s ≤ successNat ⌊n⌋₊ r then
    (Nat.find h : ℝ)
  else 0

/-- The number of runs of heads (`true`) of a sequence of tosses: of its maximal blocks of heads. -/
def runs {n : ℕ} (s : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n => s i = true ∧ ∀ h : 0 < (i : ℕ), s ⟨i - 1, by omega⟩ = false).card

/-- The expected number of runs of heads in `n` fair tosses: over the `2^n` equally likely
sequences. -/
def expectedRuns (n : ℝ) : ℝ :=
  (∑ s : Fin ⌊n⌋₊ → Bool, (runs s : ℝ)) / (Fintype.card (Fin ⌊n⌋₊ → Bool) : ℝ)

end

end Leanify.ClassicalProbability
