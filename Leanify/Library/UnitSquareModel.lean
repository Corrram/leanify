import Leanify.Library.UnitSquare
import Leanify.Denote
import Leanify.Tactic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
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
* it has *uniform marginals* when `γ([0,u] × [0,1]) = u` and `γ([0,1] × [0,v]) = v`;
* the integral of `f` *against a distribution function* `F` is the Bochner integral of `f`
  for the probability measure whose distribution function is `F`. -/

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
/-- Borel measurable real functions on `[0,1]`. -/
abbrev Interval.borelReal : (I → ℝ) → Prop := fun f => Measurable f

def distFn2 (F : I → I → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ u v : I, F u v = (μ (Set.Iic u ×ˢ Set.Iic v)).toReal

/-- The probability measure on `[0,1]^2` whose distribution function is `F` (the zero
measure when `F` is not a distribution function; the compiler asks for
`integrableAgainst`, which says that it is one). A measure on `[0,1]^2` is determined by
its values on the rectangles `[0,u] × [0,v]`, so the choice is of the only one. -/
noncomputable def measureOf (F : I → I → ℝ) : Measure (I × I) := by
  classical
  exact if h : distFn2 F then Classical.choose h else 0

/-- `\int_{[0,1]^2} f(u,v)\,\mathrm{d}F(u,v)`: the integral of `f` against the measure of
the distribution function `F`. -/
noncomputable def integralAgainst (F : I → I → ℝ) (f : I → I → ℝ) : ℝ :=
  ∫ p, f p.1 p.2 ∂(measureOf F)

/-- `F` is a distribution function on `[0,1]^2`, and `f` is integrable for its measure. -/
def integrableAgainst (F : I → I → ℝ) (f : I → I → ℝ) : Prop :=
  distFn2 F ∧ Integrable (fun p : I × I => f p.1 p.2) (measureOf F)

/-- `p` holds at almost every point of `[0,1]^2`, for the measure of the distribution
function `F`. -/
def aeAgainst (F : I → I → ℝ) (p : I → I → Prop) : Prop :=
  Filter.Eventually (fun q : I × I => p q.1 q.2) (MeasureTheory.ae (measureOf F))

/-- The Markov product of two functions on the square (Darsow, Nguyen and Olsen):
`(A * B)(u,v) = ∫₀¹ ∂₂A(u,t) ∂₁B(t,v) dt`. For copulas the two derivatives exist at almost
every `t`, and the product is the copula of `(X₀,X₂)` for a Markov chain whose steps have
the copulas `A` and `B`. The vocabulary gives the phrase to copulas only. -/
noncomputable def markovProd (A B : I → I → ℝ) : I → I → ℝ := fun u v =>
  ∫ t in (0:ℝ)..1, deriv (fun s : ℝ => A u (Interval.point s)) t *
    deriv (fun s : ℝ => B (Interval.point s) v) t

/-- The Markov product of `n` factors `C` (for `n = 0`, the unit `M(u,v) = min(u,v)` of
the product). -/
noncomputable def markovPow (C : I → I → ℝ) : ℕ → I → I → ℝ
  | 0 => fun u v => min (Interval.val u) (Interval.val v)
  | n + 1 => markovProd (markovPow C n) C

/-- The Markov power of order `k` of `C`, for a natural number `k` given as a real number. -/
noncomputable def markovPowerOf (C : I → I → ℝ) (k : ℝ) : I → I → ℝ := markovPow C (Nat.floor k)

/-- The law of a sample: a sequence of independent observations `(U_i, V_i)`,
`i = 0, 1, 2, …`, each with the distribution function `F` (the product measure of
countably many copies of the measure of `F`; the zero measure when `F` is not a
distribution function: the compiler asks for `sampleIntegrable` or `sampleHasProbability`, which
say that it is one). -/
noncomputable def sampleLaw (F : I → I → ℝ) : Measure (ℕ → I × I) := by
  classical
  exact if h : IsProbabilityMeasure (measureOf F) then
    (haveI : IsProbabilityMeasure (measureOf F) := h
     Measure.infinitePi (fun _ : ℕ => measureOf F))
  else 0

/-- The first coordinates of a sample, as a sequence indexed by real numbers (`U_i` is its
value at `i`; the compiler uses it at natural numbers). -/
noncomputable def sampleU (ω : ℕ → I × I) : ℝ → I := fun x => (ω (Nat.floor x)).1
/-- The second coordinates of a sample. -/
noncomputable def sampleV (ω : ℕ → I × I) : ℝ → I := fun x => (ω (Nat.floor x)).2

/-- `\mathbb{E}_F[X]`: the expectation of a function `X` of the sample. -/
noncomputable def sampleExpectation (F : I → I → ℝ) (X : (ℝ → I) → (ℝ → I) → ℝ) : ℝ :=
  ∫ ω, X (sampleU ω) (sampleV ω) ∂(sampleLaw F)

/-- `F` is a distribution function on `[0,1]^2`, and `X` is integrable for the law of the
sample. -/
def sampleIntegrable (F : I → I → ℝ) (X : (ℝ → I) → (ℝ → I) → ℝ) : Prop :=
  distFn2 F ∧ Integrable (fun ω : ℕ → I × I => X (sampleU ω) (sampleV ω)) (sampleLaw F)

/-- `P_F(E)`: the probability of a condition `E` on the sample. -/
noncomputable def sampleProbability (F : I → I → ℝ) (E : (ℝ → I) → (ℝ → I) → Prop) : ℝ :=
  ((sampleLaw F) {ω : ℕ → I × I | E (sampleU ω) (sampleV ω)}).toReal

/-- `F` is a distribution function on `[0,1]^2`, and the condition `E` on the sample has a
probability (it describes a measurable set, up to a set of probability zero). -/
def sampleHasProbability (F : I → I → ℝ) (E : (ℝ → I) → (ℝ → I) → Prop) : Prop :=
  distFn2 F ∧ NullMeasurableSet {ω : ℕ → I × I | E (sampleU ω) (sampleV ω)} (sampleLaw F)

/-- Two sequences have the same terms at the indices below `m`. -/
def agreeBelow (m : ℕ) (x y : ℝ → I) : Prop := ∀ i : ℕ, i < m → x i = y i

/-- A sequence in `[0,1]` indexed by the natural numbers, as one indexed by the real
numbers (its term at `x` is the term at the integer part of `x`: the compiler uses it at
natural numbers). -/
noncomputable def seqOf (s : ℕ → I) : ℝ → I := fun x => s (Nat.floor x)

/-- The law of a sequence of independent terms, each uniform on `[0,1]`. -/
noncomputable def uniformLaw : Measure (ℕ → I) := Measure.infinitePi (fun _ : ℕ => (volume : Measure I))

instance : IsProbabilityMeasure uniformLaw := by
  unfold uniformLaw
  infer_instance

/-- A kernel: a function of finitely many terms of a sequence in `[0,1]`, measurable and
square-integrable for independent uniform terms (a function in `L²([0,1]^m)` for some
`m`). -/
def isKernel (F : (ℝ → I) → ℝ) : Prop :=
  (∃ m : ℕ, ∀ x y, agreeBelow m x y → F x = F y) ∧
  AEStronglyMeasurable (fun s : ℕ → I => F (seqOf s)) uniformLaw ∧
  Integrable (fun s : ℕ → I => F (seqOf s) ^ 2) uniformLaw

/-- A statistic: a function of finitely many observations of a sample that is measurable
in them. -/
def isStatistic (T : (ℝ → I) → (ℝ → I) → ℝ) : Prop :=
  (∃ m : ℕ, ∀ x y x' y', agreeBelow m x x' → agreeBelow m y y' → T x y = T x' y') ∧
  Measurable (fun ω : ℕ → I × I => T (sampleU ω) (sampleV ω))

/-- `F` has a bounded density: `F(u,v) = ∫₀ᵘ∫₀ᵛ c(s,t) dt ds` for a bounded measurable `c`. -/
def hasBoundedDensity (F : I → I → ℝ) : Prop :=
  ∃ c : ℝ → ℝ → ℝ, Measurable (fun p : ℝ × ℝ => c p.1 p.2) ∧ (∃ B : ℝ, ∀ s t, |c s t| ≤ B) ∧
    ∀ u v : I, F u v = ∫ s in (0:ℝ)..(Interval.val u), ∫ t in (0:ℝ)..(Interval.val v), c s t

instance (F : I → I → ℝ) : IsFiniteMeasure (measureOf F) := by
  unfold measureOf
  split
  · rename_i h
    have := (Classical.choose_spec h).1
    infer_instance
  · infer_instance

/-- The conditional distribution function of the second coordinate given the first, for
the measure of a distribution function `F`: `h_F(u,v) = P(V ≤ v | U = u)`, from the
disintegration of the measure (Mathlib's `Measure.condKernel`). For a copula `C` it is a
version of the partial derivative `∂₁C`. -/
noncomputable def conditionalDF (F : I → I → ℝ) : I → I → ℝ := fun u v =>
  ((measureOf F).condKernel u (Set.Iic v)).toReal

open Classical in
/-- The quantile function of the standard normal distribution on `(0,1)`:
`Φ⁻¹(u) = inf {x : u ≤ Φ(x)}` for the standard normal distribution function `Φ` (Mathlib's
`cdf (gaussianReal 0 1)`), and `0` at the two end points. For `0 < u < 1`, it is the
number `x` with `Φ(x) = u`. -/
noncomputable def normalQuantile (u : I) : ℝ :=
  if 0 < (u : ℝ) ∧ (u : ℝ) < 1 then
    sInf {x : ℝ | (u : ℝ) ≤ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x}
  else 0

def dfUniformMarginals (F : I → I → ℝ) : Prop :=
  (∀ u : I, F u 1 = u) ∧ ∀ v : I, F 1 v = v

def probMeasure2 (γ : (I → I → Prop) → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ A : I → I → Prop, MeasurableSet {p : I × I | A p.1 p.2} →
      γ A = (μ {p : I × I | A p.1 p.2}).toReal

def measUniformMarginals (γ : (I → I → Prop) → ℝ) : Prop :=
  (∀ u : I, γ (fun x _ => x ≤ u) = u) ∧ ∀ v : I, γ (fun _ z => z ≤ v) = v

/-! ## Facts about distribution functions, their measures and samples

What the proofs of an article use about the meanings above, and what `definedness`
uses through `leanify_facts`: a distribution function is measurable and takes values in
`[0,1]`, its measure is a probability measure, a function of one coordinate has the
integral of the function when the marginals are uniform, and the law of a sample is a
probability measure. -/

-- (the alternatives of a `first` that a later version of Mathlib no longer needs)
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- A distribution function takes values in `[0,1]`. -/
theorem distFn2_bounds {F : I → I → ℝ} (h : distFn2 F) (u v : I) : 0 ≤ F u v ∧ F u v ≤ 1 := by
  obtain ⟨μ, hμ, hF⟩ := h
  have := hμ
  rw [hF u v]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h1 : μ (Set.Iic u ×ˢ Set.Iic v) ≤ 1 := prob_le_one
  have h2 := ENNReal.toReal_mono ENNReal.one_ne_top h1
  simpa using h2

/-- A distribution function is measurable, as a function of the point of the square. -/
theorem distFn2_measurable {F : I → I → ℝ} (h : distFn2 F) : Measurable (fun p : I × I => F p.1 p.2) := by
  obtain ⟨μ, hμ, hF⟩ := h
  have := hμ
  have hS : MeasurableSet {q : (I × I) × (I × I) | q.2.1 ≤ q.1.1 ∧ q.2.2 ≤ q.1.2} :=
    (measurableSet_le (by fun_prop) (by fun_prop)).inter (measurableSet_le (by fun_prop) (by fun_prop))
  have hm := measurable_measure_prodMk_left (ν := μ) hS
  have he : (fun p : I × I => F p.1 p.2) =
      fun p => (μ (Prod.mk p ⁻¹' {q : (I × I) × (I × I) | q.2.1 ≤ q.1.1 ∧ q.2.2 ≤ q.1.2})).toReal := by
    funext p
    rw [hF p.1 p.2]
    congr 2
  rw [he]
  exact hm.ennreal_toReal

/-- The measure of a distribution function is a probability measure. -/
theorem measureOf_prob {F : I → I → ℝ} (h : distFn2 F) : IsProbabilityMeasure (measureOf F) := by
  unfold measureOf
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).1

/-- A distribution function is the measure of the rectangles `[0,u] × [0,v]`. -/
theorem measureOf_apply {F : I → I → ℝ} (h : distFn2 F) (u v : I) :
    F u v = ((measureOf F) (Set.Iic u ×ˢ Set.Iic v)).toReal := by
  have h1 : measureOf F = Classical.choose h := by
    unfold measureOf
    rw [dite_eq_left h]
  rw [h1]
  exact (Classical.choose_spec h).2 u v

/-- A bounded measurable function is integrable for a finite measure. -/
theorem integrable_of_bounded {α : Type} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

/-- An expression in a distribution function `F` and the coordinates that is measurable
and bounded is integrable against `F` (the two properties may use that `F` is measurable
and takes values in `[0,1]`). -/
theorem integrableAgainst_of_bounded {F f : I → I → ℝ} (hF : distFn2 F) (B : ℝ)
    (h : (Measurable fun p : I × I => F p.1 p.2) → (∀ u v : I, 0 ≤ F u v ∧ F u v ≤ 1) →
      (Measurable fun p : I × I => f p.1 p.2) ∧ ∀ u v : I, |f u v| ≤ B) :
    integrableAgainst F f := by
  have := measureOf_prob hF
  obtain ⟨hm, hb⟩ := h (distFn2_measurable hF) (distFn2_bounds hF)
  exact ⟨hF, integrable_of_bounded hm B fun p => hb p.1 p.2⟩

/-- The first marginal of a distribution function with uniform marginals is Lebesgue
measure. -/
theorem measureOf_map_fst {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) :
    (measureOf C).map Prod.fst = volume := by
  have := measureOf_prob h.1
  have := Measure.isFiniteMeasure_map (measureOf C) (Prod.fst : I × I → I)
  refine Measure.ext_of_Iic _ _ (fun a => ?_)
  rw [Measure.map_apply measurable_fst measurableSet_Iic, unitInterval.volume_Iic]
  have h1 : ((Prod.fst : I × I → I) ⁻¹' Set.Iic a) = Set.Iic a ×ˢ Set.Iic (1 : I) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_prod]
    exact ⟨fun hp => ⟨hp, unitInterval.le_one'⟩, fun hp => hp.1⟩
  rw [h1]
  have h2 := measureOf_apply h.1 a 1
  rw [h.2.1 a] at h2
  rw [h2, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The second marginal of a distribution function with uniform marginals is Lebesgue
measure. -/
theorem measureOf_map_snd {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) :
    (measureOf C).map Prod.snd = volume := by
  have := measureOf_prob h.1
  have := Measure.isFiniteMeasure_map (measureOf C) (Prod.snd : I × I → I)
  refine Measure.ext_of_Iic _ _ (fun a => ?_)
  rw [Measure.map_apply measurable_snd measurableSet_Iic, unitInterval.volume_Iic]
  have h1 : ((Prod.snd : I × I → I) ⁻¹' Set.Iic a) = Set.Iic (1 : I) ×ˢ Set.Iic a := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_prod]
    exact ⟨fun hp => ⟨unitInterval.le_one', hp⟩, fun hp => hp.2⟩
  rw [h1]
  have h2 := measureOf_apply h.1 1 a
  rw [h.2.2 a] at h2
  rw [h2, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- With uniform marginals, an integrable function of the first coordinate is integrable
for the measure of the distribution function. -/
theorem integrable_fst {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) {g : I → ℝ}
    (hg : Measurable g) (hi : Integrable g) : Integrable (fun p : I × I => g p.1) (measureOf C) := by
  have h1 : Integrable g ((measureOf C).map Prod.fst) := by rw [measureOf_map_fst h]; exact hi
  exact (integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable).mp h1

/-- With uniform marginals, an integrable function of the second coordinate is integrable
for the measure of the distribution function. -/
theorem integrable_snd {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) {g : I → ℝ}
    (hg : Measurable g) (hi : Integrable g) : Integrable (fun p : I × I => g p.2) (measureOf C) := by
  have h1 : Integrable g ((measureOf C).map Prod.snd) := by rw [measureOf_map_snd h]; exact hi
  exact (integrable_map_measure hg.aestronglyMeasurable measurable_snd.aemeasurable).mp h1

/-- With uniform marginals, a function of the first coordinate has the integral of the
function. -/
theorem integral_fst {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) {g : I → ℝ}
    (hg : Measurable g) : ∫ p : I × I, g p.1 ∂(measureOf C) = ∫ x, g x := by
  rw [← measureOf_map_fst h]
  exact (integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable).symm

/-- With uniform marginals, a function of the second coordinate has the integral of the
function. -/
theorem integral_snd {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) {g : I → ℝ}
    (hg : Measurable g) : ∫ p : I × I, g p.2 ∂(measureOf C) = ∫ x, g x := by
  rw [← measureOf_map_snd h]
  exact (integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable).symm

/-- The product `u v` is a distribution function: that of Lebesgue measure on the square. -/
theorem distFn2_mul : distFn2 (fun u v : I => (u : ℝ) * (v : ℝ)) := by
  refine ⟨(volume : Measure I).prod volume, inferInstance, fun u v => ?_⟩
  show (u : ℝ) * (v : ℝ) = _
  rw [Measure.prod_prod, unitInterval.volume_Iic, unitInterval.volume_Iic, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal u.2.1, ENNReal.toReal_ofReal v.2.1]

/-- The product `u v` has uniform marginals. -/
theorem dfUniformMarginals_mul : dfUniformMarginals (fun u v : I => (u : ℝ) * (v : ℝ)) := by
  refine ⟨fun u => ?_, fun v => ?_⟩
  · show (u : ℝ) * ((1 : I) : ℝ) = (u : ℝ)
    rw [show ((1 : I) : ℝ) = 1 from rfl, mul_one]
  · show ((1 : I) : ℝ) * (v : ℝ) = (v : ℝ)
    rw [show ((1 : I) : ℝ) = 1 from rfl, one_mul]

/-- The product `u v` has the bounded density `1`. -/
theorem hasBoundedDensity_mul : hasBoundedDensity (fun u v : I => (u : ℝ) * (v : ℝ)) := by
  refine ⟨fun _ _ => 1, measurable_const, ⟨1, fun _ _ => by norm_num⟩, fun u v => ?_⟩
  simp

/-- The law of a sample is a probability measure. -/
theorem sampleLaw_prob {F : I → I → ℝ} (h : distFn2 F) : IsProbabilityMeasure (sampleLaw F) := by
  have := measureOf_prob h
  unfold sampleLaw
  split
  · infer_instance
  · rename_i hn
    exact absurd (measureOf_prob h) hn

/-- The law of a sample is a finite measure (the zero measure, when the function is not a
distribution function). -/
theorem sampleLaw_finite (F : I → I → ℝ) : IsFiniteMeasure (sampleLaw F) := by
  unfold sampleLaw
  split
  · infer_instance
  · infer_instance

/-- A term of the first coordinates of a sample is a measurable function of the sample. -/
theorem sampleU_measurable (y : ℝ) : Measurable (fun ω : ℕ → I × I => ((sampleU ω y : I) : ℝ)) :=
  measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply _))

/-- A term of the second coordinates of a sample is a measurable function of the sample. -/
theorem sampleV_measurable (y : ℝ) : Measurable (fun ω : ℕ → I × I => ((sampleV ω y : I) : ℝ)) :=
  measurable_subtype_coe.comp (measurable_snd.comp (measurable_pi_apply _))

/-- A larger event has a larger probability. -/
theorem sampleProbability_mono (F : I → I → ℝ) {E E' : (ℝ → I) → (ℝ → I) → Prop}
    (h : ∀ U V, E U V → E' U V) : sampleProbability F E ≤ sampleProbability F E' := by
  have := sampleLaw_finite F
  unfold sampleProbability
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => h _ _ hω)

/-- An event that always holds has probability `1`. -/
theorem sampleProbability_always {F : I → I → ℝ} (hF : distFn2 F) {p : Prop} (hp : p) :
    sampleProbability F (fun _ _ => p) = 1 := by
  have := sampleLaw_prob hF
  show ((sampleLaw F) {ω : ℕ → I × I | p}).toReal = 1
  have h : {ω : ℕ → I × I | p} = Set.univ := Set.eq_univ_of_forall fun _ => hp
  rw [h, measure_univ]
  simp

/-- An event that is a measurable set of samples has a probability. -/
theorem sampleHasProbability_of_measurableSet {F : I → I → ℝ} (hF : distFn2 F)
    {E : (ℝ → I) → (ℝ → I) → Prop} (h : MeasurableSet {ω : ℕ → I × I | E (sampleU ω) (sampleV ω)}) :
    sampleHasProbability F E :=
  ⟨hF, h.nullMeasurableSet⟩

/-- The event that a measurable statistic is within `e` of `t` has a probability. -/
theorem sampleHasProbability_abs_sub_lt {F : I → I → ℝ} (hF : distFn2 F) {T : (ℝ → I) → (ℝ → I) → ℝ}
    (hT : Measurable fun ω : ℕ → I × I => T (sampleU ω) (sampleV ω)) (e t : ℝ) :
    sampleHasProbability F (fun U V => |T U V - t| < e) := by
  have hs : MeasurableSet {ω : ℕ → I × I | |T (sampleU ω) (sampleV ω) - t| < e} :=
    measurableSet_lt (continuous_abs.measurable.comp (hT.sub measurable_const)) measurable_const
  exact ⟨hF, hs.nullMeasurableSet⟩

/-- The complement of a deviation: if a measurable statistic is at least `e` away from `t`
with probability at most `a`, it is within `e` of `t` with probability at least `1 - a`. -/
theorem sampleProbability_abs_sub_lt {F : I → I → ℝ} (hF : distFn2 F) {T : (ℝ → I) → (ℝ → I) → ℝ}
    (hT : Measurable fun ω : ℕ → I × I => T (sampleU ω) (sampleV ω)) (e t a : ℝ)
    (h : sampleProbability F (fun U V => e ≤ |T U V - t|) ≤ a) :
    1 - a ≤ sampleProbability F (fun U V => |T U V - t| < e) := by
  have := sampleLaw_prob hF
  obtain ⟨S, hS⟩ : ∃ S : Set (ℕ → I × I), S = {ω | e ≤ |T (sampleU ω) (sampleV ω) - t|} := ⟨_, rfl⟩
  have hs : MeasurableSet S := by
    rw [hS]
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp (hT.sub measurable_const))
  have h1 : (sampleLaw F) S + (sampleLaw F) Sᶜ = 1 := by
    rw [measure_add_measure_compl hs, measure_univ]
  have h2 := congrArg ENNReal.toReal h1
  have h3 : (1 : ENNReal).toReal = 1 := by simp
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h3] at h2
  have hh : sampleProbability F (fun U V => e ≤ |T U V - t|) = ((sampleLaw F) S).toReal := by
    rw [hS]
    rfl
  have hg : sampleProbability F (fun U V => |T U V - t| < e) = ((sampleLaw F) Sᶜ).toReal := by
    rw [hS]
    show ((sampleLaw F) {ω : ℕ → I × I | |T (sampleU ω) (sampleV ω) - t| < e}).toReal = _
    congr 2
    ext ω
    first
      | exact not_le.symm
      | simp
  rw [hg]
  rw [hh] at h
  linarith

/-- A distribution function increases in its first argument. -/
theorem distFn2_mono_fst {C : I → I → ℝ} (hC : distFn2 C) {u u' : I} (h : u' ≤ u) (v : I) :
    C u' v ≤ C u v := by
  have := measureOf_prob hC
  have e1 := measureOf_apply hC u' v
  have e2 := measureOf_apply hC u v
  rw [e1, e2]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.prod_mono (Set.Iic_subset_Iic.mpr h) subset_rfl))

/-- A distribution function increases in its second argument. -/
theorem distFn2_mono_snd {C : I → I → ℝ} (hC : distFn2 C) (u : I) {v v' : I} (h : v' ≤ v) :
    C u v' ≤ C u v := by
  have := measureOf_prob hC
  have e1 := measureOf_apply hC u v'
  have e2 := measureOf_apply hC u v
  rw [e1, e2]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.prod_mono subset_rfl (Set.Iic_subset_Iic.mpr h)))

/-- With uniform marginals, a distribution function grows at most as fast as its first
argument. -/
theorem distFn2_incr_fst {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) {u u' : I}
    (hu : u' ≤ u) (v : I) : C u v - C u' v ≤ (u : ℝ) - (u' : ℝ) := by
  have := measureOf_prob h.1
  have e1 := measureOf_apply h.1 u v
  have e2 := measureOf_apply h.1 u' 1
  have e3 := measureOf_apply h.1 u 1
  have e4 := measureOf_apply h.1 u' v
  have m1 := h.2.1 u
  have m2 := h.2.1 u'
  have key : (measureOf C) (Set.Iic u ×ˢ Set.Iic v) + (measureOf C) (Set.Iic u' ×ˢ Set.Iic (1 : I)) ≤
      (measureOf C) (Set.Iic u ×ˢ Set.Iic (1 : I)) + (measureOf C) (Set.Iic u' ×ˢ Set.Iic v) := by
    rw [← measure_union_add_inter _ (measurableSet_Iic.prod measurableSet_Iic)]
    refine add_le_add (measure_mono ?_) (measure_mono ?_)
    · rintro p (hp | hp)
      · exact ⟨hp.1, unitInterval.le_one'⟩
      · exact ⟨le_trans hp.1 hu, hp.2⟩
    · rintro p ⟨hp1, hp2⟩
      exact ⟨hp2.1, hp1.2⟩
  have k2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) key
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← e1, ← e2, ← e3, ← e4, m1, m2] at k2
  linarith

/-- With uniform marginals, a distribution function grows at most as fast as its second
argument. -/
theorem distFn2_incr_snd {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) (u : I) {v v' : I}
    (hv : v' ≤ v) : C u v - C u v' ≤ (v : ℝ) - (v' : ℝ) := by
  have := measureOf_prob h.1
  have e1 := measureOf_apply h.1 u v
  have e2 := measureOf_apply h.1 1 v'
  have e3 := measureOf_apply h.1 1 v
  have e4 := measureOf_apply h.1 u v'
  have m1 := h.2.2 v
  have m2 := h.2.2 v'
  have key : (measureOf C) (Set.Iic u ×ˢ Set.Iic v) + (measureOf C) (Set.Iic (1 : I) ×ˢ Set.Iic v') ≤
      (measureOf C) (Set.Iic (1 : I) ×ˢ Set.Iic v) + (measureOf C) (Set.Iic u ×ˢ Set.Iic v') := by
    rw [← measure_union_add_inter _ (measurableSet_Iic.prod measurableSet_Iic)]
    refine add_le_add (measure_mono ?_) (measure_mono ?_)
    · rintro p (hp | hp)
      · exact ⟨unitInterval.le_one', hp.2⟩
      · exact ⟨hp.1, le_trans hp.2 hv⟩
    · rintro p ⟨hp1, hp2⟩
      exact ⟨hp1.1, hp2.2⟩
  have k2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) key
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← e1, ← e2, ← e3, ← e4, m1, m2] at k2
  linarith

/-- With uniform marginals, a distribution function is Lipschitz: it changes by at most the
changes of its two arguments. -/
theorem distFn2_abs_sub_le {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) (u u' v v' : I) :
    |C u v - C u' v'| ≤ |(u : ℝ) - (u' : ℝ)| + |(v : ℝ) - (v' : ℝ)| := by
  have h1 : |C u v - C u' v| ≤ |(u : ℝ) - (u' : ℝ)| := by
    rcases le_total u' u with hu | hu
    · have a := distFn2_incr_fst h hu v
      have b := distFn2_mono_fst h.1 hu v
      rw [abs_le]
      constructor <;>
        linarith [abs_nonneg ((u : ℝ) - (u' : ℝ)), le_abs_self ((u : ℝ) - (u' : ℝ)),
          neg_abs_le ((u : ℝ) - (u' : ℝ))]
    · have a := distFn2_incr_fst h hu v
      have b := distFn2_mono_fst h.1 hu v
      rw [abs_le]
      constructor <;>
        linarith [abs_nonneg ((u : ℝ) - (u' : ℝ)), le_abs_self ((u : ℝ) - (u' : ℝ)),
          neg_abs_le ((u : ℝ) - (u' : ℝ))]
  have h2 : |C u' v - C u' v'| ≤ |(v : ℝ) - (v' : ℝ)| := by
    rcases le_total v' v with hv | hv
    · have a := distFn2_incr_snd h u' hv
      have b := distFn2_mono_snd h.1 u' hv
      rw [abs_le]
      constructor <;>
        linarith [abs_nonneg ((v : ℝ) - (v' : ℝ)), le_abs_self ((v : ℝ) - (v' : ℝ)),
          neg_abs_le ((v : ℝ) - (v' : ℝ))]
    · have a := distFn2_incr_snd h u' hv
      have b := distFn2_mono_snd h.1 u' hv
      rw [abs_le]
      constructor <;>
        linarith [abs_nonneg ((v : ℝ) - (v' : ℝ)), le_abs_self ((v : ℝ) - (v' : ℝ)),
          neg_abs_le ((v : ℝ) - (v' : ℝ))]
  have h3 := abs_add_le (C u v - C u' v) (C u' v - C u' v')
  have h4 : C u v - C u' v + (C u' v - C u' v') = C u v - C u' v' := by ring
  rw [h4] at h3
  linarith

/-- With uniform marginals, a distribution function is continuous on the square. -/
theorem distFn2_continuous {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) :
    Continuous (fun p : I × I => C p.1 p.2) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun p q => ?_).continuous
  have hl := distFn2_abs_sub_le h p.1 q.1 p.2 q.2
  have h1 : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h2 : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  rw [Subtype.dist_eq, Real.dist_eq] at h1 h2
  have h3 : ((2 : NNReal) : ℝ) = 2 := by norm_num
  rw [Real.dist_eq, h3]
  linarith

/-- The first coordinates of a sample of a distribution function with uniform marginals
are independent and uniform. -/
theorem sampleLaw_map_fst {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) :
    (sampleLaw C).map (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).1) = uniformLaw := by
  have hp := measureOf_prob h.1
  have e : sampleLaw C = Measure.infinitePi (fun _ : ℕ => measureOf C) := by
    unfold sampleLaw
    split
    · rfl
    · rename_i hn
      exact absurd hp hn
  have key := Measure.infinitePi_map_pi (μ := fun _ : ℕ => measureOf C)
    (f := fun _ : ℕ => (Prod.fst : I × I → I)) (fun _ => measurable_fst)
  rw [e]
  refine key.trans ?_
  rw [measureOf_map_fst h]
  rfl

/-- The second coordinates of a sample of a distribution function with uniform marginals
are independent and uniform. -/
theorem sampleLaw_map_snd {C : I → I → ℝ} (h : distFn2 C ∧ dfUniformMarginals C) :
    (sampleLaw C).map (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).2) = uniformLaw := by
  have hp := measureOf_prob h.1
  have e : sampleLaw C = Measure.infinitePi (fun _ : ℕ => measureOf C) := by
    unfold sampleLaw
    split
    · rfl
    · rename_i hn
      exact absurd hp hn
  have key := Measure.infinitePi_map_pi (μ := fun _ : ℕ => measureOf C)
    (f := fun _ : ℕ => (Prod.snd : I × I → I)) (fun _ => measurable_snd)
  rw [e]
  refine key.trans ?_
  rw [measureOf_map_snd h]
  rfl

/-- A kernel of the first coordinates of a sample is measurable and square-integrable,
for a distribution function with uniform marginals. -/
theorem isKernel_fst {F : (ℝ → I) → ℝ} (hF : isKernel F) {C : I → I → ℝ}
    (h : distFn2 C ∧ dfUniformMarginals C) :
    AEStronglyMeasurable (fun ω : ℕ → I × I => F (sampleU ω)) (sampleLaw C) ∧
      Integrable (fun ω : ℕ → I × I => F (sampleU ω) ^ 2) (sampleLaw C) := by
  have hπ : Measurable (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).1) := by
    fun_prop
  have hm := sampleLaw_map_fst h
  have h1 : AEStronglyMeasurable (fun s : ℕ → I => F (seqOf s))
      ((sampleLaw C).map (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).1)) := by
    rw [hm]
    exact hF.2.1
  have h2 : Integrable (fun s : ℕ → I => F (seqOf s) ^ 2)
      ((sampleLaw C).map (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).1)) := by
    rw [hm]
    exact hF.2.2
  exact ⟨h1.comp_measurable hπ, h2.comp_measurable hπ⟩

/-- A kernel of the second coordinates of a sample is measurable and square-integrable,
for a distribution function with uniform marginals. -/
theorem isKernel_snd {F : (ℝ → I) → ℝ} (hF : isKernel F) {C : I → I → ℝ}
    (h : distFn2 C ∧ dfUniformMarginals C) :
    AEStronglyMeasurable (fun ω : ℕ → I × I => F (sampleV ω)) (sampleLaw C) ∧
      Integrable (fun ω : ℕ → I × I => F (sampleV ω) ^ 2) (sampleLaw C) := by
  have hπ : Measurable (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).2) := by
    fun_prop
  have hm := sampleLaw_map_snd h
  have h1 : AEStronglyMeasurable (fun s : ℕ → I => F (seqOf s))
      ((sampleLaw C).map (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).2)) := by
    rw [hm]
    exact hF.2.1
  have h2 : Integrable (fun s : ℕ → I => F (seqOf s) ^ 2)
      ((sampleLaw C).map (fun (ω : ℕ → I × I) (i : ℕ) => (ω i).2)) := by
    rw [hm]
    exact hF.2.2
  exact ⟨h1.comp_measurable hπ, h2.comp_measurable hπ⟩

/-- The product of a kernel of the first coordinates and of the second coordinates of a
sample has an expectation, for a distribution function with uniform marginals. -/
theorem isKernel_sampleIntegrable_mul {F : (ℝ → I) → ℝ} (hF : isKernel F) {C : I → I → ℝ}
    (h : distFn2 C ∧ dfUniformMarginals C) : sampleIntegrable C (fun U V => F U * F V) := by
  obtain ⟨hU, hU2⟩ := isKernel_fst hF h
  obtain ⟨hV, hV2⟩ := isKernel_snd hF h
  refine ⟨h.1, Integrable.mono' (hU2.add hV2) (hU.mul hV) (Filter.Eventually.of_forall fun ω => ?_)⟩
  show ‖F (sampleU ω) * F (sampleV ω)‖ ≤ F (sampleU ω) ^ 2 + F (sampleV ω) ^ 2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;>
    nlinarith [sq_nonneg (F (sampleU ω) - F (sampleV ω)), sq_nonneg (F (sampleU ω) + F (sampleV ω))]

/-- A kernel of the first coordinates of a sample has an expectation, for a distribution
function with uniform marginals. -/
theorem isKernel_sampleIntegrable {F : (ℝ → I) → ℝ} (hF : isKernel F) {C : I → I → ℝ}
    (h : distFn2 C ∧ dfUniformMarginals C) : sampleIntegrable C (fun U _ => F U) := by
  have := sampleLaw_finite C
  obtain ⟨hU, hU2⟩ := isKernel_fst hF h
  refine ⟨h.1, Integrable.mono' ((integrable_const (1 : ℝ)).add hU2) hU
    (Filter.Eventually.of_forall fun ω => ?_)⟩
  show ‖F (sampleU ω)‖ ≤ 1 + F (sampleU ω) ^ 2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;>
    nlinarith [sq_nonneg (F (sampleU ω) - 1), sq_nonneg (F (sampleU ω) + 1), sq_nonneg (F (sampleU ω))]

/-! ### Events and statistics of a sample are measurable

`leanify_sample_fun` proves that a real expression in the terms of a sample (sums,
products, differences, quotients, maxima, absolute values, powers, finite sums and case
distinctions between such expressions) is a measurable function of the sample, and
`leanify_sample_event` that a comparison of two such expressions is a measurable set of
samples. `leanify_facts` uses them: a condition on such expressions has a probability. -/

/-- `leanify_sample_fun` proves `Measurable fun ω => e` for an expression `e` in the terms
`sampleU ω i`, `sampleV ω i` of a sample `ω`. -/
syntax "leanify_sample_fun" : tactic
/-- `leanify_sample_event` proves `MeasurableSet {ω | e₁ ≤ e₂}` (or `<`, `=`) for
expressions in the terms of a sample `ω`. -/
syntax "leanify_sample_event" : tactic

namespace Meas
variable {Ω ι : Type} [MeasurableSpace Ω]

/-! The steps of the two tactics, each stated for an expression as it is written (`fun ω =>
f ω + g ω`), so that a step fits an expression by its form alone. -/
theorem add {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω + g ω :=
  hf.add hg
theorem sub {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω - g ω :=
  hf.sub hg
theorem mul {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω * g ω :=
  hf.mul hg
theorem div {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω / g ω :=
  hf.div hg
theorem neg {f : Ω → ℝ} (hf : Measurable f) : Measurable fun ω => -f ω :=
  hf.neg
theorem max {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun ω => Max.max (f ω) (g ω) :=
  hf.max hg
theorem min {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun ω => Min.min (f ω) (g ω) :=
  hf.min hg
theorem abs {f : Ω → ℝ} (hf : Measurable f) : Measurable fun ω => |f ω| :=
  continuous_abs.measurable.comp hf
theorem rpow {f : Ω → ℝ} {q : ℝ} (hq : 0 ≤ q) (hf : Measurable f) : Measurable fun ω => f ω ^ q :=
  (Real.continuous_rpow_const hq).measurable.comp hf
theorem pow {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) : Measurable fun ω => f ω ^ n :=
  hf.pow_const n
theorem sum (s : Finset ι) {f : ι → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun ω => ∑ i ∈ s, f i ω :=
  Finset.measurable_fun_sum s fun i _ => hf i
theorem ite {p : Ω → Prop} {d : DecidablePred p} {f g : Ω → ℝ} (hp : MeasurableSet {ω | p ω})
    (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => @_root_.ite ℝ (p ω) (d ω) (f ω) (g ω) :=
  Measurable.ite hp hf hg
theorem lt {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {ω | f ω < g ω} :=
  measurableSet_lt hf hg
theorem le {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {ω | f ω ≤ g ω} :=
  measurableSet_le hf hg

end Meas

-- (every step is tried without unfolding definitions: a step that does not fit the
-- expression fails at once, and does not unfold the expression to see whether it fits)
macro_rules
  | `(tactic| leanify_sample_event) => `(tactic| first
      | with_reducible_and_instances exact MeasurableSet.const _
      | ((with_reducible_and_instances refine Meas.lt ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.le ?_ ?_) <;> leanify_sample_fun))

macro_rules
  | `(tactic| leanify_sample_fun) => `(tactic| first
      | with_reducible_and_instances exact measurable_const
      | with_reducible_and_instances exact sampleU_measurable _
      | with_reducible_and_instances exact sampleV_measurable _
      | with_reducible_and_instances assumption
      | ((with_reducible_and_instances refine Meas.add ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.sub ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.mul ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.div ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.neg ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.max ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.min ?_ ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.abs ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.rpow ?_ ?_) <;> first | leanify_sample_fun | (norm_num; done))
      | ((with_reducible_and_instances refine Meas.pow ?_ _) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.sum _ fun _ => ?_) <;> leanify_sample_fun)
      | ((with_reducible_and_instances refine Meas.ite ?_ ?_ ?_) <;>
          first | leanify_sample_event | leanify_sample_fun)
      | (unfold Leanify.Prelude.finSum; leanify_sample_fun))

/-- (for `definedness`) A comparison of two expressions in the terms of a sample has a
probability. -/
macro_rules
  | `(tactic| leanify_facts) => `(tactic|
      (with_reducible refine sampleHasProbability_of_measurableSet ?_ ?_
       · first | assumption | leanify_part
       · try beta_reduce
         leanify_sample_event))

/-- A constant is a kernel. -/
theorem isKernel_const (c : ℝ) : isKernel (fun _ => c) :=
  ⟨⟨0, fun _ _ _ => rfl⟩, aestronglyMeasurable_const, integrable_const _⟩

/-- A constant is a statistic. -/
theorem isStatistic_const (c : ℝ) : isStatistic (fun _ _ => c) :=
  ⟨⟨0, fun _ _ _ _ _ _ => rfl⟩, measurable_const⟩

/-- (for `definedness`) An integral against a distribution function of an expression in it
and the coordinates that is measurable and at most `4` in absolute value: the hypotheses
give the distribution function, `fun_prop` the measurability and `nlinarith` the bound. -/
macro_rules
  | `(tactic| leanify_facts) => `(tactic|
      (with_reducible refine integrableAgainst_of_bounded ?_ 4 ?_
       · first | assumption | leanify_part
       · intro hm hb
         refine ⟨by fun_prop, fun u v => ?_⟩
         rw [abs_le]
         constructor <;>
           nlinarith [(hb u v).1, (hb u v).2, u.2.1, u.2.2, v.2.1, v.2.2,
             mul_nonneg u.2.1 v.2.1, mul_le_mul u.2.2 v.2.2 v.2.1 zero_le_one]))

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
    ⟨set2 ⟶ .prop, Prelude.measurableSet2⟩, ⟨set1 ⟶ .real, Prelude.leb⟩, ⟨self ⟶ .prop, Interval.borel⟩,
    ⟨sq ⟶ sq ⟶ .real, integralAgainst⟩, ⟨sq ⟶ sq ⟶ .prop, integrableAgainst⟩,
    ⟨(I01 ⟶ .real) ⟶ .prop, Interval.borelReal⟩,
    ⟨sq ⟶ (I01 ⟶ I01 ⟶ .prop) ⟶ .prop, aeAgainst⟩,
    ⟨sq ⟶ sq ⟶ sq, markovProd⟩, ⟨sq ⟶ .real ⟶ sq, markovPowerOf⟩,
    ⟨sq ⟶ (seq ⟶ seq ⟶ .real) ⟶ .real, sampleExpectation⟩, ⟨sq ⟶ (seq ⟶ seq ⟶ .real) ⟶ .prop, sampleIntegrable⟩,
    ⟨sq ⟶ (seq ⟶ seq ⟶ .prop) ⟶ .real, sampleProbability⟩, ⟨sq ⟶ (seq ⟶ seq ⟶ .prop) ⟶ .prop, sampleHasProbability⟩,
    ⟨(seq ⟶ .real) ⟶ .prop, isKernel⟩, ⟨(seq ⟶ seq ⟶ .real) ⟶ .prop, isStatistic⟩,
    ⟨sq ⟶ .prop, hasBoundedDensity⟩, ⟨sq ⟶ sq, conditionalDF⟩, ⟨I01 ⟶ .real, normalQuantile⟩]

end Leanify.UnitSquare
