import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Moments.Variance
import Leanify.Denote

/-! # The meaning of the field `poissonprocesses`

The Poisson process with rate `λ` built from its interarrival times: independent exponential
times `E₁, E₂, …` with rate `λ` (Mathlib `expMeasure`, `Measure.infinitePi`), the `k`th arrival at
`E₁ + … + E_k` and the number `N_t` of arrivals by time `t`. Each arrival of the thinned process
is kept with probability `p`, independently; its rate is its mean number of arrivals per unit
time. A compound Poisson sum adds independent jumps of a law with the given mean and variance at
the arrivals; its mean and variance are the same for every such law. The formulas
(`e^{-λt}(λt)^k/k!`, `1 - e^{-λt}`, `k/λ`, `∑_{j<k} e^{-λt}(λt)^j/j!`, `pλ`, `λtμ`,
`λt(σ² + μ²)`) are theorems, not definitions. -/

namespace Leanify.PoissonProcesses

noncomputable section
open MeasureTheory ProbabilityTheory

/-- The sequences of independent exponential interarrival times with rate `λ`. -/
def interarrivals (rate : ℝ) : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => expMeasure rate

/-- The time of the `k`th arrival: the sum of the first `k` interarrival times. -/
def arrival (E : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, E i

/-- The number of arrivals by time `t`. -/
def count (E : ℕ → ℝ) (t : ℝ) : ℕ∞ := ⨆ (k : ℕ) (_ : 1 ≤ k ∧ arrival E k ≤ t), (k : ℕ∞)

/-- The probability of `k` arrivals by time `t` at rate `λ`. -/
def probArrivals (k t rate : ℝ) : ℝ := (interarrivals rate {E | count E t = (⌊k⌋₊ : ℕ∞)}).toReal

/-- The probability of an arrival by time `t` at rate `λ`. -/
def probSomeArrival (t rate : ℝ) : ℝ := (interarrivals rate {E | 1 ≤ count E t}).toReal

/-- The expected waiting time for the `k`th arrival at rate `λ`. -/
def waiting (k rate : ℝ) : ℝ := ∫ E, arrival E ⌊k⌋₊ ∂(interarrivals rate)

/-- The probability that the `k`th arrival comes after time `t` at rate `λ`. -/
def probLate (k t rate : ℝ) : ℝ := (interarrivals rate {E | t < arrival E ⌊k⌋₊}).toReal

/-- A step of the thinning: kept (`true`) with probability `p`. -/
def keep (p : ℝ) : Measure Bool := ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The interarrival times with the marks of the thinning. -/
def thinned (rate p : ℝ) : Measure (ℕ → ℝ × Bool) := Measure.infinitePi fun _ => (expMeasure rate).prod (keep p)

/-- The number of kept arrivals by time `t`. -/
def keptCount (ω : ℕ → ℝ × Bool) (t : ℝ) : ℕ∞ :=
  ((Set.ncard {k : ℕ | 1 ≤ k ∧ arrival (fun i => (ω i).1) k ≤ t ∧ (ω (k - 1)).2 = true} : ℕ) : ℕ∞)

/-- The rate of the process with rate `λ` thinned with probability `p`: its mean number of arrivals
by time `1`. -/
def thinnedRate (rate p : ℝ) : ℝ := (∫⁻ ω, (keptCount ω 1 : ENNReal) ∂(thinned rate p)).toReal

/-- The interarrival times with independent jumps of the law `ν`. -/
def compound (rate : ℝ) (ν : Measure ℝ) : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi fun _ => (expMeasure rate).prod ν

/-- The compound Poisson sum at time `t`: the sum of the jumps at the arrivals by `t`. -/
def compoundSum (ω : ℕ → ℝ × ℝ) (t : ℝ) : ℝ := by
  classical exact
  ∑' k : ℕ, if arrival (fun i => (ω i).1) (k + 1) ≤ t then (ω k).2 else 0

/-- `ν` is a law of the jumps with mean `m` and variance `v`. -/
def IsJumpLaw (ν : Measure ℝ) (m v : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ MemLp id 2 ν ∧ ∫ y, y ∂ν = m ∧ ∫ y, (y - m) ^ 2 ∂ν = v

/-- The value of a quantity of the compound sums for every law of the jumps with mean `m` and
variance `v` (`0` where there is none, or they differ). -/
def ofJumps (m v : ℝ) (f : Measure ℝ → ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, (∃ ν, IsJumpLaw ν m v) ∧ ∀ ν, IsJumpLaw ν m v → f ν = c then Classical.choose h else 0

/-- The mean of the compound Poisson sum at time `t` with rate `λ` and jump mean `m` (for every
law of the jumps with that mean and a finite variance). -/
def compoundMean (t rate m : ℝ) : ℝ := by
  classical exact
  if h : ∃ c : ℝ, ∀ ν v, IsJumpLaw ν m v → ∫ ω, compoundSum ω t ∂(compound rate ν) = c then Classical.choose h else 0

/-- The variance of the compound Poisson sum at time `t` with rate `λ`, jump mean `m` and jump
variance `v`. -/
def compoundVariance (t rate m v : ℝ) : ℝ :=
  ofJumps m v fun ν => variance (fun ω => compoundSum ω t) (compound rate ν)

end

end Leanify.PoissonProcesses
