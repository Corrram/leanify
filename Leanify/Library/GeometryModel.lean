import Leanify.Denote
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The meaning of the field `geometry`

A point is a pair of real numbers, with the Euclidean distance. -/

namespace Leanify.Geometry

/-- A point of the plane. -/
def Point : Type := ℝ × ℝ

def Point.origin : Point := ((0 : ℝ), (0 : ℝ))

noncomputable section

def point (x y : ℝ) : Point := (x, y)
def xCoord (p : Point) : ℝ := p.1
def yCoord (p : Point) : ℝ := p.2
def dist (a b : Point) : ℝ := Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2)
def midpoint (a b : Point) : Point := ((a.1 + b.1) / 2, (a.2 + b.2) / 2)
def area (a b c : Point) : ℝ := |(b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)| / 2
/-- The angle at `b` between `a` and `c`, in `[0, π]`. -/
def angle (b a c : Point) : ℝ :=
  Real.arccos (((a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2)) / (dist a b * dist c b))
def Collinear (a b c : Point) : Prop := (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2)
def centroid (a b c : Point) : Point := ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)

end

end Leanify.Geometry
