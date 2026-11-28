import Leanify.Library.VectorsModel
import Leanify.Library.MatricesModel
import Leanify.Library.LinearSystemsModel
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The meaning of the field `randomvectors`

A random vector is a function of the outcome `ω` of one probability space for the whole
article, `[0,1]` with Lebesgue measure, into the real vectors (`Leanify.Vectors.Vec`, of the
field `vectors`; matrices are those of `matrices`, complex numbers Mathlib's). Its
dimension is that of its value at the outcome `0`; a random vector (`IsRVec`) has this
dimension at every outcome, and measurable coordinates. Every joint distribution of finitely
or countably many random vectors is the distribution of functions on this space, so a
statement about the distributions of the random vectors of an article means the same on it
as on any other probability space that carries them.

Distributions are compared by joint distribution functions, which determine them:
`P(X ≤ t)` is the measure of the outcomes in `[0,1]` at which every coordinate of `X` is at
most that of `t`. -/

namespace Leanify.RandomVectors

/-- A random vector: a function of the outcome `ω ∈ [0,1]` (its values elsewhere are not
used). -/
def RVec : Type := ℝ → Leanify.Vectors.Vec

/-- The random vector of dimension 0. -/
def RVec.zero : RVec := fun _ => Leanify.Vectors.Vec.empty

noncomputable section
open Classical MeasureTheory

/-- The number of coordinates. -/
def size (X : RVec) : ℕ := (X 0).1

/-- The coordinate at `i` of the value at `ω` (`0` outside). -/
def coordAt (X : RVec) (i : ℕ) (ω : ℝ) : ℝ := Leanify.Vectors.at' (X ω) i

def dim (X : RVec) : ℝ := (size X : ℝ)

/-- `X_i(ω)`, for the `i`-th coordinate, `1 ≤ i ≤ d`. -/
def coord (X : RVec) (i ω : ℝ) : ℝ := coordAt X (⌊i⌋₊ - 1) ω

/-- `X` is a random vector: of one dimension, with (Borel) measurable coordinates. -/
def IsRVec (X : RVec) : Prop :=
  (∀ ω : ℝ, (X ω).1 = size X) ∧ ∀ i : ℕ, Measurable (fun ω : ℝ => coordAt X i ω)

def ofReal (c : ℝ) : RVec := fun _ => Leanify.Vectors.ofReal c
def SameDim (X Y : RVec) : Prop := size X = size Y
/-- `XY` is defined: one of them has dimension 1. -/
def Scalable (X Y : RVec) : Prop := size X = 1 ∨ size Y = 1

def add (X Y : RVec) : RVec := fun ω => Leanify.Vectors.add (X ω) (Y ω)
def sub (X Y : RVec) : RVec := fun ω => Leanify.Vectors.sub (X ω) (Y ω)
def neg (X : RVec) : RVec := fun ω => Leanify.Vectors.neg (X ω)
def mul (X Y : RVec) : RVec := fun ω => Leanify.Vectors.mul (X ω) (Y ω)

/-- The outcomes at which `X ≤ t`, coordinatewise. -/
def below (X : RVec) (t : Leanify.Vectors.Vec) : Set ℝ :=
  {ω : ℝ | 0 ≤ ω ∧ ω ≤ 1 ∧ ∀ i : ℕ, i < size X → coordAt X i ω ≤ Leanify.Vectors.at' t i}

/-- `P(X ≤ t)`: the joint distribution function. -/
def cdf (X : RVec) (t : Leanify.Vectors.Vec) : ℝ := (volume (below X t)).toReal

/-- `F` is the joint distribution function of `X`. -/
def HasCdf (X : RVec) (F : Leanify.Vectors.Vec → ℝ) : Prop := ∀ t : Leanify.Vectors.Vec, cdf X t = F t

/-- The vector `b` as the constant random vector. -/
def ofVec (b : Leanify.Vectors.Vec) : RVec := fun _ => b

/-- `AX` is defined: `A` has as many columns as `X` has coordinates. -/
def Actable (A : Leanify.Matrices.Mat) (X : RVec) : Prop := A.2.1 = size X

/-- `AX`: the matrix `A` applied to the value at every outcome. -/
def act (A : Leanify.Matrices.Mat) (X : RVec) : RVec := fun ω => Leanify.LinearSystems.mulVec A (X ω)

/-- The characteristic function `t ↦ E[e^{i⟨t,X⟩}]` (as Mathlib's `MeasureTheory.charFun` of
the distribution of `X`). -/
def charFun (X : RVec) (t : Leanify.Vectors.Vec) : ℂ :=
  MeasureTheory.integral
    (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (0 : ℝ) 1))
    (fun ω : ℝ => Complex.exp (Complex.I * ((Leanify.Vectors.inner (X ω) t : ℝ) : ℂ)))

/-- The expectation of a real function of the outcome. -/
def expect (f : ℝ → ℝ) : ℝ :=
  MeasureTheory.integral
    (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (0 : ℝ) 1)) f

/-- The mean vector: the expectations of the coordinates. -/
def mean (X : RVec) : Leanify.Vectors.Vec :=
  Leanify.Vectors.mk (size X) fun i => expect (coordAt X i)

/-- The covariance matrix: the covariances of the coordinates. -/
def cov (X : RVec) : Leanify.Matrices.Mat :=
  Leanify.Matrices.mk (size X) (size X) fun i j =>
    expect (fun ω => (coordAt X i ω - expect (coordAt X i)) * (coordAt X j ω - expect (coordAt X j)))

/-- The same distribution: the same dimension and the same joint distribution function. -/
def EqDist (X Y : RVec) : Prop :=
  size X = size Y ∧ ∀ t : Leanify.Vectors.Vec, cdf X t = cdf Y t

/-- Independent: the joint distribution function of the coordinates of both is the product
of theirs. -/
def Indep (X Y : RVec) : Prop :=
  ∀ s t : Leanify.Vectors.Vec, (volume (below X s ∩ below Y t)).toReal = cdf X s * cdf Y t

end

end Leanify.RandomVectors
