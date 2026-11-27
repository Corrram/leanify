import Leanify.Library.Core

/-! # Vocabulary: lattice points

Counts of integer points in plane and space regions, and Pick's theorem (`We write $N(r)$ for
the number of lattice points in the disk of radius $r$.`).

* notions: the number of points of `ℤ²` in the closed disk of radius `r` about the origin
  (Gauss's circle problem) and of `ℤ³` in the closed ball; the number of lattice points on the
  segment from the origin to `(a,b)`; the number of visible lattice points `(a,b)` with
  `1 ≤ a, b ≤ n` (no lattice point strictly between them and the origin); the area of a lattice
  polygon with `I` interior and `B` boundary points. The greatest common divisor itself is in
  the field `numbers`.

The quantities are constants, interpreted by the declarations of
`Leanify/Library/LatticePointsModel.lean`: the number of elements of `ℤ²` and `ℤ³` with the
property (`Nat.card`), and the Lebesgue measure of the region of a simple closed polygonal curve
with vertices in `ℤ²` (the curve and the bounded components of its complement). The formulas
(`gcd(a,b) + 1`, coprime coordinates, Pick's `I + B/2 - 1`) are theorems, not definitions. -/

namespace Leanify.LatticePoints
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def notBoth (a b : B) : B := and (and (isInt a) (isInt b)) (or (ne a (num 0)) (ne b (num 0)))

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def diskPoints : Nat := 0
def ballPoints : Nat := 1
def segmentPoints : Nat := 2
def visiblePoints : Nat := 3
def pickArea : Nat := 4
def existsPolygon : Nat := 5
end Const

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .prop]
  constNames := [w!"\\#(\\mathbb{Z}^2\\cap D_{#})", w!"\\#(\\mathbb{Z}^3\\cap B_{#})", w!"\\#(\\mathbb{Z}^2\\cap[0,(#1,#2)])",
    w!"\\operatorname{vis}", w!"\\operatorname{area}_{#1,#2}", w!"\\exists P_{#1,#2}"]
  constLean := [w!"Leanify.LatticePoints.diskPoints", w!"Leanify.LatticePoints.ballPoints",
    w!"Leanify.LatticePoints.segmentPoints", w!"Leanify.LatticePoints.visiblePoints", w!"Leanify.LatticePoints.pickArea",
    w!"Leanify.LatticePoints.ExistsLatticePolygon"]
  modules := [w!"Leanify.Library.LatticePointsModel"]
  notions := [
    { name := phrase!"number of lattice points in the disk of radius $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r],
      doc := "the number of `(a,b) ∈ ℤ²` with `a² + b² ≤ r²` (Gauss's circle problem)", value := .const Const.diskPoints },
    { name := phrase!"number of lattice points in the ball of radius $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r],
      doc := "the number of `(a,b,c) ∈ ℤ³` with `a² + b² + c² ≤ r²`", value := .const Const.ballPoints },
    { name := phrase!"number of lattice points on the segment from the origin to the point with coordinates $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt, dom2 .real fun a b => notBoth a b],
      doc := "the points of `ℤ²` on the segment, its ends included (`gcd(a,b) + 1`)", value := .const Const.segmentPoints },
    { name := phrase!"number of visible lattice points in the square of side $v$", ty := .real ⟶ .real,
      doms := [dom1 .real natP],
      doc := "the `(a,b)` with `1 ≤ a, b ≤ n` with no lattice point strictly between them and the origin (`gcd(a,b) = 1`)",
      value := .const Const.visiblePoints },
    { name := phrase!"area of a lattice polygon with $v$ interior points and $v$ boundary points", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun i b => and (and (isInt b) (le (num 3) b)) (app2 (const Const.existsPolygon) i b)],
      doc := "the Lebesgue measure of the region of a simple lattice polygon with these points, where there is one (`I + B/2 - 1`, Pick)",
      value := .const Const.pickArea }]

end Leanify.LatticePoints
