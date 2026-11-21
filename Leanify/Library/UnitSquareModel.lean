import Leanify.Library.UnitSquare
import Leanify.Denote
import Leanify.Tactic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.ProductMeasure
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

/-- A kernel: a function of finitely many terms of a sequence in `[0,1]`, measurable and
square-integrable for independent uniform terms (a function in `L²([0,1]^m)` for some
`m`). -/
def isKernel (F : (ℝ → I) → ℝ) : Prop :=
  (∃ m : ℕ, ∀ x y, agreeBelow m x y → F x = F y) ∧
  AEStronglyMeasurable (fun ω : ℕ → I × I => F (sampleU ω))
    (sampleLaw (fun u v => Interval.val u * Interval.val v)) ∧
  Integrable (fun ω : ℕ → I × I => F (sampleU ω) ^ 2)
    (sampleLaw (fun u v => Interval.val u * Interval.val v))

/-- A statistic: a function of finitely many observations of a sample that is measurable
in them. -/
def isStatistic (T : (ℝ → I) → (ℝ → I) → ℝ) : Prop :=
  (∃ m : ℕ, ∀ x y x' y', agreeBelow m x x' → agreeBelow m y y' → T x y = T x' y') ∧
  Measurable (fun ω : ℕ → I × I => T (sampleU ω) (sampleV ω))

/-- `F` has a bounded density: `F(u,v) = ∫₀ᵘ∫₀ᵛ c(s,t) dt ds` for a bounded measurable `c`. -/
def hasBoundedDensity (F : I → I → ℝ) : Prop :=
  ∃ c : ℝ → ℝ → ℝ, Measurable (fun p : ℝ × ℝ => c p.1 p.2) ∧ (∃ B : ℝ, ∀ s t, |c s t| ≤ B) ∧
    ∀ u v : I, F u v = ∫ s in (0:ℝ)..(Interval.val u), ∫ t in (0:ℝ)..(Interval.val v), c s t

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

/-- A constant is a kernel. -/
theorem isKernel_const (c : ℝ) : isKernel (fun _ => c) := by
  have := sampleLaw_finite (fun u v => Interval.val u * Interval.val v)
  exact ⟨⟨0, fun _ _ _ => rfl⟩, aestronglyMeasurable_const, integrable_const _⟩

/-- A constant is a statistic. -/
theorem isStatistic_const (c : ℝ) : isStatistic (fun _ _ => c) :=
  ⟨⟨0, fun _ _ _ _ _ _ => rfl⟩, measurable_const⟩

/-- (for `definedness`) An integral against a distribution function of an expression in it
and the coordinates that is measurable and at most `4` in absolute value: the hypotheses
give the distribution function, `fun_prop` the measurability and `nlinarith` the bound. -/
macro_rules
  | `(tactic| leanify_facts) => `(tactic|
      (refine integrableAgainst_of_bounded (by first | assumption | leanify_part) 4
          (fun hm hb => ⟨by fun_prop, fun u v => ?_⟩)
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
    ⟨sq ⟶ .prop, hasBoundedDensity⟩]

end Leanify.UnitSquare
