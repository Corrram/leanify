import Leanify.Syntax
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # The meaning of core terms

`denote M G L t` is the value of the term `t`, where `M` interprets the
vocabulary (its base types and constants), `G` are the values of the article's
definitions and `L` those of the bound variables. -/

namespace Leanify
open MeasureTheory
open scoped unitInterval

/-- The meaning of a type, given the meanings `B` of the vocabulary's base types. -/
@[reducible] def Ty.denote (B : Nat → Type) : Ty → Type
  | .real => ℝ
  | .unit => I
  | .prop => Prop
  | .fn a b => a.denote B → b.denote B
  | .base k => B k
  | .complex => ℂ

/-- A value of every type (used for ill-typed or undefined terms). -/
def Ty.default {B : Nat → Type} (d : (k : Nat) → B k) : (t : Ty) → t.denote B
  | .real => (0 : ℝ)
  | .unit => (0 : I)
  | .prop => False
  | .fn _ b => fun _ => Ty.default d b
  | .base k => d k
  | .complex => (0 : ℂ)

/-- A typed value. -/
abbrev Val (B : Nat → Type) := Σ t : Ty, t.denote B

/-- The interpretation of a vocabulary: the Lean types of its base types and the
Lean values of its constants. A vocabulary without base types uses `B k = Unit`. -/
structure Model where
  base : Nat → Type
  default : (k : Nat) → base k
  consts : List (Val base)

/-- The model of an empty vocabulary. -/
def Model.empty : Model := ⟨fun _ => Unit, fun _ => (), []⟩

namespace Prelude
noncomputable def leb (A : I → Prop) : ℝ := (volume {x : I | A x}).toReal
def measurableSet1 (A : I → Prop) : Prop := MeasurableSet {x : I | A x}
def measurableSet2 (A : I → I → Prop) : Prop := MeasurableSet {p : I × I | A p.1 p.2}
def integrable (f : I → ℝ) : Prop := Integrable f
def hasDerivWithin (f : ℝ → ℝ) (S : ℝ → Prop) (x d : ℝ) : Prop :=
  HasDerivWithinAt f d {y | S y} x
noncomputable def intervalIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, f t
/-- `x` is an integer. -/
def isInt (x : ℝ) : Prop := ∃ k : ℤ, (k : ℝ) = x
/-- `x` is a natural number `0, 1, 2, …`. -/
def isNat (x : ℝ) : Prop := ∃ k : ℕ, (k : ℝ) = x
/-- The largest integer at most `x`. -/
noncomputable def floor (x : ℝ) : ℝ := ((Int.floor x : ℤ) : ℝ)
/-- The smallest integer at least `x`. -/
noncomputable def ceil (x : ℝ) : ℝ := ((Int.ceil x : ℤ) : ℝ)
/-- `∑_{k=a}^{b} f(k)` over the integers `k` with `a ≤ k ≤ b`. -/
noncomputable def finSum (a b : ℝ) (f : ℝ → ℝ) : ℝ := Finset.sum (Finset.Icc (Int.ceil a) (Int.floor b)) (fun k : ℤ => f (k : ℝ))
/-- `∏_{k=a}^{b} f(k)` over the integers `k` with `a ≤ k ≤ b`. -/
noncomputable def finProd (a b : ℝ) (f : ℝ → ℝ) : ℝ := Finset.prod (Finset.Icc (Int.ceil a) (Int.floor b)) (fun k : ℤ => f (k : ℝ))
/-- The partial sums `∑_{n<N} f(a+n)` of the series `∑_{k=a}^∞ f(k)`. -/
noncomputable def partialSum (a : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun n : ℕ => f (((Int.ceil a : ℤ) : ℝ) + (n : ℝ)))
/-- The series converges: its partial sums have a limit. -/
def seriesConv (a : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (partialSum a f) Filter.atTop (nhds L)
/-- The sum of the series: the limit of its partial sums. -/
noncomputable def series (a : ℝ) (f : ℝ → ℝ) : ℝ := Filter.limUnder Filter.atTop (partialSum a f)
/-- `f(x)` has a limit as `x → a` within `D \ {a}`, and `a` is a limit point of `D`. -/
def limAtConv (a : ℝ) (D : ℝ → Prop) (f : ℝ → ℝ) : Prop :=
  (nhdsWithin a ({x | D x} \ {a})).NeBot ∧
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin a ({x | D x} \ {a})) (nhds L)
/-- The limit of `f(x)` as `x → a` within `D \ {a}`. -/
noncomputable def limAt (a : ℝ) (D : ℝ → Prop) (f : ℝ → ℝ) : ℝ :=
  Filter.limUnder (nhdsWithin a ({x | D x} \ {a})) f
/-- `f(x)` has a limit as `x → ∞` within `D`, and `D` is unbounded above. -/
def limTopConv (D : ℝ → Prop) (f : ℝ → ℝ) : Prop :=
  (Filter.atTop ⊓ Filter.principal {x | D x}).NeBot ∧
    ∃ L : ℝ, Filter.Tendsto f (Filter.atTop ⊓ Filter.principal {x | D x}) (nhds L)
/-- The limit of `f(x)` as `x → ∞` within `D`. -/
noncomputable def limTop (D : ℝ → Prop) (f : ℝ → ℝ) : ℝ :=
  Filter.limUnder (Filter.atTop ⊓ Filter.principal {x | D x}) f
/-- `x^k` for an integer `k`. -/
noncomputable def zpow (x k : ℝ) : ℝ := x ^ (Int.floor k)
/-- `n!` for a natural number `n` (as a real number). -/
noncomputable def factorial (x : ℝ) : ℝ := ((Nat.factorial (Nat.floor x) : ℕ) : ℝ)
/-- `\binom{n}{k}` for natural numbers `n`, `k` (as a real number). -/
noncomputable def binom (x y : ℝ) : ℝ := ((Nat.choose (Nat.floor x) (Nat.floor y) : ℕ) : ℝ)
def intervalIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop := IntervalIntegrable f volume a b
def compact2 (S : ℝ → ℝ → Prop) : Prop := IsCompact {p : ℝ × ℝ | S p.1 p.2}
def convex2 (S : ℝ → ℝ → Prop) : Prop := Convex ℝ {p : ℝ × ℝ | S p.1 p.2}
def symm2 (S : ℝ → ℝ → Prop) : Prop := ∀ a b, S a b → S (-a) (-b)
def continuousOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ContinuousOn f {x | D x}
def concaveOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ConcaveOn ℝ {x | D x} f
def strictMonoOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := StrictMonoOn f {x | D x}

/-! Standard properties of a real function on a domain. `increasing` alone is
not one of them (it is used for both `StrictMonoOn` and `MonotoneOn`). -/
def convexOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ConvexOn ℝ {x | D x} f
def strictConvexOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := StrictConvexOn ℝ {x | D x} f
def strictConcaveOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := StrictConcaveOn ℝ {x | D x} f
def strictAntiOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := StrictAntiOn f {x | D x}
def monotoneOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := MonotoneOn f {x | D x}
def antitoneOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := AntitoneOn f {x | D x}
def boundedOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop :=
  BddAbove (f '' {x | D x}) ∧ BddBelow (f '' {x | D x})
def nonnegOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ∀ x, D x → 0 ≤ f x
def posOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ∀ x, D x → 0 < f x
def differentiableOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := DifferentiableOn ℝ f {x | D x}
/-- Continuously differentiable: of class `C¹`. -/
def contDiffOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ContDiffOn ℝ 1 f {x | D x}
def injOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := Set.InjOn f {x | D x}
def lowerSemicontinuousOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := LowerSemicontinuousOn f {x | D x}
def upperSemicontinuousOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := UpperSemicontinuousOn f {x | D x}
def lipschitzOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ∃ K : NNReal, LipschitzOnWith K f {x | D x}

/-! Standard properties of a set of points of the plane. -/
def closed2 (S : ℝ → ℝ → Prop) : Prop := IsClosed {p : ℝ × ℝ | S p.1 p.2}
def open2 (S : ℝ → ℝ → Prop) : Prop := IsOpen {p : ℝ × ℝ | S p.1 p.2}
def bounded2 (S : ℝ → ℝ → Prop) : Prop := Bornology.IsBounded {p : ℝ × ℝ | S p.1 p.2}
def connected2 (S : ℝ → ℝ → Prop) : Prop := IsConnected {p : ℝ × ℝ | S p.1 p.2}

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

/-! Functions of several variables: a curried function of `n` real variables is a
function on `Fin n → ℝ` (with the supremum norm and the product Lebesgue measure). -/

/-- The uncurried form of a function of `n` real variables. -/
def uncurryN {B : Nat → Type} : (n : Nat) → (Ty.fns n).denote B → (Fin n → ℝ) → ℝ
  | 0, f, _ => f
  | n + 1, f, p => uncurryN n (f (p 0)) (fun i => p i.succ)

/-- The set of points of `ℝⁿ` of a curried predicate. -/
def setOfN {B : Nat → Type} : (n : Nat) → (Ty.setN n).denote B → Set (Fin n → ℝ)
  | 0, S => {_p | S}
  | n + 1, S => {p | (fun i => p i.succ) ∈ setOfN n (S (p 0))}

def smoothN {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (S : (Ty.setN n).denote B) : Prop :=
  ∀ k : ℕ, ContDiffOn ℝ k (uncurryN n f) (setOfN n S)
def compactSuppIn {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (S : (Ty.setN n).denote B) : Prop :=
  HasCompactSupport (uncurryN n f) ∧ tsupport (uncurryN n f) ⊆ setOfN n S
def supportIn {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (S : (Ty.setN n).denote B) : Prop :=
  tsupport (uncurryN n f) ⊆ setOfN n S
def isCompactN {B : Nat → Type} (n : Nat) (S : (Ty.setN n).denote B) : Prop :=
  IsCompact (setOfN n S)
/-- `‖f‖_{L²(ℝⁿ)} = r` (the norm is finite). -/
def l2NormN {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (r : ℝ) : Prop :=
  eLpNorm (uncurryN n f) 2 volume = ENNReal.ofReal r ∧ 0 ≤ r
/-- `‖f‖_{L^∞(ℝⁿ)} = r` (the essential supremum of `|f|` is finite). -/
def supNormN {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (r : ℝ) : Prop :=
  eLpNorm (uncurryN n f) ⊤ volume = ENNReal.ofReal r ∧ 0 ≤ r
/-- `f` is smooth and `g` gives its partial derivatives of every order:
`g(I, x) = ∂^I f(x)` for a multi-index `I ∈ ℕⁿ`, and `0` at any other first argument. -/
def partialMulti {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (g : (Ty.fns (n + n)).denote B) : Prop :=
  (∀ k : ℕ, ContDiff ℝ k (uncurryN n f)) ∧
  ∀ p : Fin (n + n) → ℝ,
    ((∀ i : Fin n, ∃ k : ℕ, p (Fin.castAdd n i) = k) →
      let L := (List.finRange n).flatMap fun i => List.replicate ⌊p (Fin.castAdd n i)⌋₊ i
      uncurryN (n + n) g p = iteratedFDeriv ℝ L.length (uncurryN n f) (fun i => p (Fin.natAdd n i))
        (fun j => Pi.single (L.get j) 1)) ∧
    ((¬ ∀ i : Fin n, ∃ k : ℕ, p (Fin.castAdd n i) = k) → uncurryN (n + n) g p = 0)
/-- The set `P` is finite and has `r` elements. -/
def cardIs (P : ℝ → Prop) (r : ℝ) : Prop := {x | P x}.Finite ∧ r = ({x | P x}.ncard : ℝ)

/-! Complex numbers. -/
def cofReal (x : ℝ) : ℂ := x
def cadd (z w : ℂ) : ℂ := z + w
def csub (z w : ℂ) : ℂ := z - w
def cmul (z w : ℂ) : ℂ := z * w
noncomputable def cdiv (z w : ℂ) : ℂ := z / w
def cneg (z : ℂ) : ℂ := -z
def cre (z : ℂ) : ℝ := z.re
def cim (z : ℂ) : ℝ := z.im
noncomputable def cabs (z : ℂ) : ℝ := ‖z‖
def cconj (z : ℂ) : ℂ := (starRingEnd ℂ) z
def cI : ℂ := Complex.I
/-- `z^r` for a natural number `r` (callers guard `r ∈ ℕ`). -/
noncomputable def cpow (z : ℂ) (r : ℝ) : ℂ := z ^ ⌊r⌋₊
noncomputable def cexp (z : ℂ) : ℂ := Complex.exp z
/-- `f` is integrable on `ℝⁿ` and `∫_{ℝⁿ} f = r`. -/
def integralN {B : Nat → Type} (n : Nat) (f : (Ty.fns n).denote B) (r : ℝ) : Prop :=
  Integrable (uncurryN n f) volume ∧ ∫ p, uncurryN n f p = r
end Prelude

def FnProp.denote : FnProp → (ℝ → ℝ) → (ℝ → Prop) → Prop
  | .convex => Prelude.convexOn
  | .strictConvex => Prelude.strictConvexOn
  | .strictConcave => Prelude.strictConcaveOn
  | .strictAnti => Prelude.strictAntiOn
  | .monotone => Prelude.monotoneOn
  | .antitone => Prelude.antitoneOn
  | .bounded => Prelude.boundedOn
  | .nonneg => Prelude.nonnegOn
  | .pos => Prelude.posOn
  | .differentiable => Prelude.differentiableOn
  | .contDiff => Prelude.contDiffOn
  | .injective => Prelude.injOn
  | .lowerSemicont => Prelude.lowerSemicontinuousOn
  | .upperSemicont => Prelude.upperSemicontinuousOn
  | .lipschitz => Prelude.lipschitzOn

def SetProp.denote : SetProp → (ℝ → ℝ → Prop) → Prop
  | .closed => Prelude.closed2
  | .isOpen => Prelude.open2
  | .bounded => Prelude.bounded2
  | .connected => Prelude.connected2

def SqProp.denote : SqProp → ((I → I → ℝ) → ℝ) → ((I → I → ℝ) → Prop) → Prop
  | .convex => Prelude.convexOnSq
  | .concave => Prelude.concaveOnSq
  | .lowerUniform => Prelude.lscUniform
  | .upperUniform => Prelude.uscUniform
  | .contUniform => Prelude.continuousUniform

def ClassProp.denote : ClassProp → ((I → I → ℝ) → Prop) → Prop
  | .convex => Prelude.convexClass
  | .compactUniform => Prelude.compactUniform
  | .closedUniform => Prelude.closedUniform

noncomputable def RealFn.denote : RealFn → ℝ → ℝ
  | .exp => Real.exp
  | .log => Real.log
  | .sin => Real.sin
  | .cos => Real.cos
  | .tan => Real.tan

noncomputable def CxOp.denote {B : Nat → Type} : (k : CxOp) → k.ty.denote B
  | .ofReal => Prelude.cofReal
  | .add => Prelude.cadd
  | .sub => Prelude.csub
  | .mul => Prelude.cmul
  | .div => Prelude.cdiv
  | .neg => Prelude.cneg
  | .re => Prelude.cre
  | .im => Prelude.cim
  | .abs => Prelude.cabs
  | .conj => Prelude.cconj
  | .I => Prelude.cI
  | .pow => Prelude.cpow
  | .exp => Prelude.cexp

noncomputable def Prim.denote {B : Nat → Type} : (p : Prim) → p.ty.denote B
  | .rpow => fun x y => x ^ y
  | .min => fun x y => Min.min x y
  | .max => fun x y => Max.max x y
  | .leb => Prelude.leb
  | .borel => fun T => Measurable T
  | .measurableSet1 => Prelude.measurableSet1
  | .measurableSet2 => Prelude.measurableSet2
  | .integrable => Prelude.integrable
  | .hasDerivWithin => Prelude.hasDerivWithin
  | .intervalIntegral => Prelude.intervalIntegral
  | .intervalIntegrable => Prelude.intervalIntegrable
  | .compact2 => Prelude.compact2
  | .convex2 => Prelude.convex2
  | .symm2 => Prelude.symm2
  | .continuousOn => Prelude.continuousOn
  | .concaveOn => Prelude.concaveOn
  | .strictMonoOn => Prelude.strictMonoOn
  | .fnProp k => k.denote
  | .setProp k => k.denote
  | .sqProp k => k.denote
  | .classProp k => k.denote
  | .realFn k => k.denote
  | .pi => Real.pi
  | .isInt => Prelude.isInt
  | .isNat => Prelude.isNat
  | .floor => Prelude.floor
  | .ceil => Prelude.ceil
  | .finSum => Prelude.finSum
  | .finProd => Prelude.finProd
  | .series => Prelude.series
  | .seriesConv => Prelude.seriesConv
  | .limAt => Prelude.limAt
  | .limAtConv => Prelude.limAtConv
  | .limTop => Prelude.limTop
  | .limTopConv => Prelude.limTopConv
  | .factorial => Prelude.factorial
  | .binom => Prelude.binom
  | .zpow => Prelude.zpow
  | .smoothN n => Prelude.smoothN n
  | .compactSuppIn n => Prelude.compactSuppIn n
  | .supportIn n => Prelude.supportIn n
  | .isCompactN n => Prelude.isCompactN n
  | .l2NormN n => Prelude.l2NormN n
  | .supNormN n => Prelude.supNormN n
  | .integralN n => Prelude.integralN n
  | .partialMulti n => Prelude.partialMulti n
  | .cardIs => Prelude.cardIs
  | .cx k => k.denote

/-- Numerals: `0`, `1` and `(n : ℝ)` for larger `n`. -/
def numVal : Nat → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((n + 2 : ℕ) : ℝ)

section
variable {B : Nat → Type}

def Val.cast (d : (k : Nat) → B k) (b : Ty) : Option (Val B) → b.denote B
  | some ⟨a, v⟩ => if h : a = b then h ▸ v else Ty.default d b
  | none => Ty.default d b

def Val.prop : Option (Val B) → Prop
  | some ⟨.prop, P⟩ => P
  | _ => False

private def real2 (x y : Option (Val B)) (f : ℝ → ℝ → ℝ) : Option (Val B) :=
  match x, y with
  | some ⟨.real, a⟩, some ⟨.real, b⟩ => some ⟨.real, f a b⟩
  | _, _ => none

private def rel2 (x y : Option (Val B)) (f : ℝ → ℝ → Prop) : Option (Val B) :=
  match x, y with
  | some ⟨.real, a⟩, some ⟨.real, b⟩ => some ⟨.prop, f a b⟩
  | _, _ => none

private def prop2 (x y : Option (Val B)) (f : Prop → Prop → Prop) : Option (Val B) :=
  match x, y with
  | some ⟨.prop, a⟩, some ⟨.prop, b⟩ => some ⟨.prop, f a b⟩
  | _, _ => none
end

/-- The meaning of a core term, given the vocabulary model, the values of article
definitions and of locals. -/
noncomputable def denote (M : Model) (G : List (Val M.base)) : List (Val M.base) → Tm → Option (Val M.base)
  | _, .glob i => G[i]?
  | L, .loc i => L[i]?
  | _, .prim p => some ⟨p.ty, p.denote⟩
  | _, .const i => M.consts[i]?
  | L, .app f x =>
    match denote M G L f, denote M G L x with
    | some ⟨.fn a b, F⟩, some ⟨a', X⟩ => if h : a' = a then some ⟨b, F (h ▸ X)⟩ else none
    | _, _ => none
  | L, .lam t _ body =>
    match typeOf (M.consts.map (·.1)) (G.map (·.1)) (t :: L.map (·.1)) body with
    | some b => some ⟨.fn t b, fun x => Val.cast M.default b (denote M G (⟨t, x⟩ :: L) body)⟩
    | none => none
  | _, .num n => some ⟨.real, numVal n⟩
  | L, .ofUnit x =>
    match denote M G L x with
    | some ⟨.unit, u⟩ => some ⟨.real, (u : ℝ)⟩
    | _ => none
  | L, .toUnit x =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.unit, Set.projIcc 0 1 zero_le_one r⟩
    | _ => none
  | L, .add x y => real2 (denote M G L x) (denote M G L y) (· + ·)
  | L, .sub x y => real2 (denote M G L x) (denote M G L y) (· - ·)
  | L, .mul x y => real2 (denote M G L x) (denote M G L y) (· * ·)
  | L, .div x y => real2 (denote M G L x) (denote M G L y) (· / ·)
  | L, .neg x =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.real, -r⟩
    | _ => none
  | L, .abs x =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.real, |r|⟩
    | _ => none
  | L, .powNat x n =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.real, r ^ n⟩
    | _ => none
  | L, .cases c v rest =>
    match denote M G L c, denote M G L v, denote M G L rest with
    | some ⟨.prop, P⟩, some ⟨a, x⟩, some ⟨b, y⟩ =>
      if h : b = a then some ⟨a, @ite _ P (Classical.propDecidable P) x (h ▸ y)⟩ else none
    | _, _, _ => none
  | _, .undef t => some ⟨t, Ty.default M.default t⟩
  | L, .eq x y =>
    match denote M G L x, denote M G L y with
    | some ⟨a, u⟩, some ⟨b, v⟩ => if h : b = a then some ⟨.prop, u = h ▸ v⟩ else none
    | _, _ => none
  | L, .lt x y => rel2 (denote M G L x) (denote M G L y) (· < ·)
  | L, .le x y => rel2 (denote M G L x) (denote M G L y) (· ≤ ·)
  | _, .tt => some ⟨.prop, True⟩
  | L, .not p =>
    match denote M G L p with
    | some ⟨.prop, P⟩ => some ⟨.prop, ¬P⟩
    | _ => none
  | L, .and p q => prop2 (denote M G L p) (denote M G L q) (· ∧ ·)
  | L, .or p q => prop2 (denote M G L p) (denote M G L q) (· ∨ ·)
  | L, .imp p q => prop2 (denote M G L p) (denote M G L q) (· → ·)
  | L, .iff p q => prop2 (denote M G L p) (denote M G L q) (· ↔ ·)
  | L, .all t body => some ⟨.prop, ∀ x : t.denote M.base, Val.prop (denote M G (⟨t, x⟩ :: L) body)⟩
  | L, .ex t body => some ⟨.prop, ∃ x : t.denote M.base, Val.prop (denote M G (⟨t, x⟩ :: L) body)⟩
  | L, .integral body =>
    some ⟨.real, ∫ x : I, Val.cast M.default .real (denote M G (⟨.unit, x⟩ :: L) body)⟩
  | L, .guard _ e => denote M G L e
  | L, .the t body =>
    some ⟨t, @Classical.epsilon (t.denote M.base) ⟨Ty.default M.default t⟩
      (fun x => Val.prop (denote M G (⟨t, x⟩ :: L) body))⟩

/-- The values of an article's definitions, evaluated in order. Definition `i`
is `Tm.glob i`; it may refer only to earlier definitions. -/
noncomputable def evalDefs (M : Model) : List (Val M.base) → List Tm → Option (List (Val M.base))
  | G, [] => some G
  | G, d :: ds =>
    match denote M G [] d with
    | some v => evalDefs M (G ++ [v]) ds
    | none => none

end Leanify
