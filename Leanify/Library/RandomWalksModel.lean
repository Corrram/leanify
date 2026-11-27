import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Leanify.Denote

/-! # The meaning of the field `randomwalks`

The simple random walk with up-probability `p` from `k`: the independent steps `±1` (`+1` with
probability `p`) under Mathlib's `Measure.infinitePi`, the position after `t` steps
`k + ∑_{i<t} ±1`; the ruin probability, the probability of reaching the target and the expected
duration are those of the events and the exit time from `(0, N)`. Brownian motion with drift
`μ` and variance `σ²` is `μt + σB_t` for a Brownian motion `B` (Mathlib `IsBrownianReal`), on any
probability space that carries one; its hitting probabilities and exit times are the same on all
of them. The transition density at time `t` is the Gaussian density of `N(μt, σ²t)` (Mathlib
`gaussianPDFReal`), the law of `μt + σB_t`. The formulas of the gambler's ruin and of the
Brownian hitting problems are theorems, not definitions. -/

namespace Leanify.RandomWalks

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A step of the walk: `+1` (`true`) with probability `p`, `-1` with probability `1 - p`. -/
def stepMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The sequences of independent steps. -/
def walkMeasure (p : ℝ) : Measure (ℕ → Bool) := Measure.infinitePi fun _ => stepMeasure p

/-- The position after `t` steps from `k`. -/
def position (k : ℤ) (ω : ℕ → Bool) (t : ℕ) : ℤ := k + ∑ i ∈ Finset.range t, if ω i then 1 else -1

/-- The walk from `k` reaches `a` at a time `t` before leaving `(0, N)`. -/
def ReachesFirst (k N a : ℤ) (ω : ℕ → Bool) : Prop :=
  ∃ t, position k ω t = a ∧ ∀ s < t, 0 < position k ω s ∧ position k ω s < N

/-- The ruin probability from `k` with target `N`: of reaching `0` before `N`. -/
def ruin (k N p : ℝ) : ℝ := (walkMeasure p {ω | ReachesFirst ⌊k⌋ ⌊N⌋ 0 ω}).toReal

/-- The probability of reaching the target `N` before `0` from `k`. -/
def reachTarget (k N p : ℝ) : ℝ := (walkMeasure p {ω | ReachesFirst ⌊k⌋ ⌊N⌋ ⌊N⌋ ω}).toReal

/-- The time at which the walk from `k` first leaves `(0, N)` (`⊤` if never). -/
def exitTime (k N : ℤ) (ω : ℕ → Bool) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : position k ω t ≤ 0 ∨ N ≤ position k ω t), (t : ℕ∞)

/-- The expected duration of the game from `k` with target `N`. -/
def duration (k N p : ℝ) : ℝ := (∫⁻ ω, (exitTime ⌊k⌋ ⌊N⌋ ω : ENNReal) ∂(walkMeasure p)).toReal

/-- The probability of being at `x` after `n` steps (from `0`). -/
def atAfter (x n p : ℝ) : ℝ := (walkMeasure p {ω | position 0 ω ⌊n⌋₊ = ⌊x⌋}).toReal

/-- The common value of a quantity of the probability spaces with a Brownian motion: for every
probability space `(Ω, P)` and Brownian motion `B` on it (`0` where there is none, or they
differ). -/
def ofBrownian (f : ∀ (Ω : Type) [MeasurableSpace Ω], Measure Ω → (ℝ≥0 → Ω → ℝ) → ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsBrownianReal B P) ∧
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P → IsBrownianReal B P → f Ω P B = c then
    Classical.choose h
  else 0

/-- The probability that Brownian motion with drift `μ` and variance `σ²` hits `a` before `c`. -/
def brownianHit (μ σ2 a c : ℝ) : ℝ := ofBrownian fun _ _ P B =>
  (P {ω | ∃ t : ℝ≥0, μ * t + Real.sqrt σ2 * B t ω = a ∧ ∀ s < t, c < μ * s + Real.sqrt σ2 * B s ω}).toReal

/-- The expected exit time of Brownian motion with variance `σ²` (no drift) from `(c, a)`, started
at `0`. -/
def brownianExit (σ2 c a : ℝ) : ℝ := ofBrownian fun _ _ P B =>
  (∫⁻ ω, ⨅ (t : ℝ≥0) (_ : Real.sqrt σ2 * B t ω ∉ Set.Ioo c a), ((t : ℝ≥0) : ENNReal) ∂P).toReal

/-- The transition density of Brownian motion with drift `μ` and variance `σ²` at time `t`: the
density of `N(μt, σ²t)`. -/
def transitionDensity (μ σ2 t : ℝ) (x : ℝ) : ℝ := gaussianPDFReal (μ * t) (Real.toNNReal (σ2 * t)) x

end

end Leanify.RandomWalks
