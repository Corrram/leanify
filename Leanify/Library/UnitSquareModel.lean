import Leanify.Library.UnitSquare
import Leanify.Denote
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
