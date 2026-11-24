import Leanify.Denote
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The meaning of the field `vectors`

A vector is a function `Fin n → ℝ`, for some `n`; its `i`-th coordinate is at `i - 1`. A real
number is the vector of dimension 1, and the product of such a vector with another is the
scalar multiple. -/

namespace Leanify.Vectors

/-- A real vector of some dimension. -/
def Vec : Type := Σ n : ℕ, Fin n → ℝ

/-- The vector of dimension 0. -/
def Vec.empty : Vec := ⟨0, fun _ => 0⟩

noncomputable section
open Classical

def dim (x : Vec) : ℝ := x.1
def ofReal (c : ℝ) : Vec := ⟨1, fun _ => c⟩
def SameDim (x y : Vec) : Prop := x.1 = y.1
/-- `xy` is defined: one of them has dimension 1. -/
def Scalable (x y : Vec) : Prop := x.1 = 1 ∨ y.1 = 1

/-- The coordinate at `i` (`0` outside). -/
def at' (x : Vec) (i : ℕ) : ℝ := if h : i < x.1 then x.2 ⟨i, h⟩ else 0
def mk (n : ℕ) (f : ℕ → ℝ) : Vec := ⟨n, fun i => f i⟩

def add (x y : Vec) : Vec := mk x.1 fun i => at' x i + at' y i
def sub (x y : Vec) : Vec := mk x.1 fun i => at' x i - at' y i
def neg (x : Vec) : Vec := mk x.1 fun i => -at' x i
def mul (x y : Vec) : Vec := if x.1 = 1 then mk y.1 fun i => at' x 0 * at' y i else mk x.1 fun i => at' y 0 * at' x i

def inner (x y : Vec) : ℝ := ∑ i ∈ Finset.range x.1, at' x i * at' y i
def norm (x : Vec) : ℝ := Real.sqrt (inner x x)
def coord (i : ℝ) (x : Vec) : ℝ := at' x (⌊i⌋₊ - 1)
def cross (x y : Vec) : Vec := mk 3 fun i =>
  at' x ((i + 1) % 3) * at' y ((i + 2) % 3) - at' x ((i + 2) % 3) * at' y ((i + 1) % 3)
def zero (n : ℝ) : Vec := mk ⌊n⌋₊ fun _ => 0
def basis (i n : ℝ) : Vec := mk ⌊n⌋₊ fun j => if j + 1 = ⌊i⌋₊ then 1 else 0
def angle (x y : Vec) : ℝ := Real.arccos (inner x y / (norm x * norm y))
def coordSum (x : Vec) : ℝ := ∑ i ∈ Finset.range x.1, at' x i
def Parallel (x y : Vec) : Prop := ∃ c : ℝ, y = mul (ofReal c) x ∨ x = mul (ofReal c) y

end

end Leanify.Vectors
