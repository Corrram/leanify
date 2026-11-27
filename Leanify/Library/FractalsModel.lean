import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Leanify.Denote

/-! # The meaning of the field `fractals`

The fractals by their constructions: Mathlib's middle-thirds Cantor set `cantorSet` and its
stages `preCantorSet n`, with its Hausdorff dimension (Mathlib `dimH`); the Koch curve and the
Koch snowflake as polygonal curves of `ℂ` (each segment replaced by four, the middle third by
the two other sides of an equilateral triangle outside), the snowflake the closure of the union
of the regions of its stages; the Sierpinski triangle and the Menger sponge as unions of scaled
copies of their stages. Lengths, areas and volumes are sums of lengths of segments and Lebesgue
measures. The formulas (`log 2/log 3`, `(2/3)^n`, `2^n`, `(4/3)^n`, `2√3 s²/5`,
`(√3/4) s² (3/4)^n`, `(20/27)^n`) are theorems, not definitions. -/

namespace Leanify.Fractals

noncomputable section
open MeasureTheory

/-- The Hausdorff dimension of the middle-thirds Cantor set. -/
def cantorDimension : ℝ := (dimH cantorSet).toReal

/-- The length of the Cantor set after `n` steps: the Lebesgue measure of its `n`th stage. -/
def cantorLength (n : ℝ) : ℝ := (volume (preCantorSet ⌊n⌋₊)).toReal

/-- The number of intervals of the Cantor set after `n` steps: of connected components of its
`n`th stage. -/
def cantorIntervals (n : ℝ) : ℝ :=
  (Nat.card {C : Set ℝ // ∃ x ∈ preCantorSet ⌊n⌋₊, C = connectedComponentIn (preCantorSet ⌊n⌋₊) x} : ℝ)

/-- A step of the Koch construction on a polygonal path: each segment `[p, q]` becomes the four
segments through its thirds `a`, `b` and the apex `c` of the equilateral triangle on `[a, b]` to
the right of the path. -/
def kochStep : List ℂ → List ℂ
  | p :: q :: rest =>
    let a := p + (q - p) / 3
    let b := p + 2 * (q - p) / 3
    let c := a + (b - a) * Complex.exp (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I)
    p :: a :: c :: b :: kochStep (q :: rest)
  | l => l

/-- The length of a polygonal path: the sum of the lengths of its segments. -/
def pathLength : List ℂ → ℝ
  | p :: q :: rest => ‖q - p‖ + pathLength (q :: rest)
  | _ => 0

/-- The points of a polygonal path: the union of its segments. -/
def pathSet : List ℂ → Set ℂ
  | p :: q :: rest => segment ℝ p q ∪ pathSet (q :: rest)
  | [p] => {p}
  | [] => ∅

/-- The length of the Koch curve after `n` steps, from the unit segment. -/
def kochLength (n : ℝ) : ℝ := pathLength (kochStep^[⌊n⌋₊] [0, 1])

/-- The region of a closed curve: the curve and the bounded connected components of its
complement. -/
def region (S : Set ℂ) : Set ℂ := S ∪ {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- The `n`th stage of the Koch snowflake on the equilateral triangle with side `s`, as a closed
path (counterclockwise, so that the triangles are added outside). -/
def snowflakeStage (s : ℝ) (n : ℕ) : List ℂ :=
  kochStep^[n] [0, (s : ℂ), (s : ℂ) * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I), 0]

/-- The area of the Koch snowflake with side `s`: the Lebesgue measure of the closure of the union
of the regions of its stages. -/
def snowflakeArea (s : ℝ) : ℝ := (volume (closure (⋃ n, region (pathSet (snowflakeStage s n))))).toReal

/-- The vertices of the equilateral triangle with side `s`. -/
def triVertices (s : ℝ) : Set ℂ := {0, (s : ℂ), (s : ℂ) * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)}

/-- The `n`th stage of the Sierpinski triangle with side `s`: the filled triangle, then the union
of its halvings towards the three vertices. -/
def sierpinski (s : ℝ) : ℕ → Set ℂ
  | 0 => convexHull ℝ (triVertices s)
  | n + 1 => ⋃ v ∈ triVertices s, (fun x => (x + v) / 2) '' sierpinski s n

/-- The area of the Sierpinski triangle with side `s` after `n` steps. -/
def sierpinskiArea (s n : ℝ) : ℝ := (volume (sierpinski s ⌊n⌋₊)).toReal

/-- The translations of the `20` subcubes kept by a step of the Menger sponge: the `t ∈ {0,1,2}³`
with at most one coordinate `1`. -/
def mengerShifts : Set (Fin 3 → ℝ) :=
  {t | (∀ i, t i = 0 ∨ t i = 1 ∨ t i = 2) ∧ ∀ i j, i ≠ j → t i = 1 → t j ≠ 1}

/-- The `n`th stage of the Menger sponge from the unit cube. -/
def menger : ℕ → Set (Fin 3 → ℝ)
  | 0 => Set.Icc 0 1
  | n + 1 => ⋃ t ∈ mengerShifts, (fun x => (x + t) / 3) '' menger n

/-- The volume of the Menger sponge after `n` steps. -/
def mengerVolume (n : ℝ) : ℝ := (volume (menger ⌊n⌋₊)).toReal

end

end Leanify.Fractals
