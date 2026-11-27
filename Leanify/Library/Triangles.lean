import Leanify.Library.Core

/-! # Vocabulary: triangles by their sides, and regular polygons

The metric quantities of a triangle with side lengths `a`, `b`, `c` (`We write $\Delta(a,b,c)$
for the area of the triangle with sides $a$, $b$ and $c$.`) and of a regular `n`-gon with side
`s`; the triangles by their points are in the field `planegeometry`.

* notions, for positive `a, b, c` with `a < b + c`, `b < a + c`, `c < a + b`: the semiperimeter
  `(a + b + c)/2`, the area, the angle opposite `c`, the inradius, the circumradius, the altitude
  to `c`, the median to `c`, the bisector of the angle opposite `c`; for a regular `n`-gon
  (`n ≥ 3`) with side `s`: the interior angle, the area, the circumradius, the apothem; and the
  number of diagonals of a convex `n`-gon. A right or an acute triangle is said by its angles
  (`the angle opposite $c$ … is $\frac{\pi}{2}$`).

Apart from the semiperimeter, the quantities are constants, interpreted by the declarations of
`Leanify/Library/TrianglesModel.lean`: their values for the triangles `PQR` of the Euclidean
plane with these sides (the Lebesgue measure of the convex hull; Mathlib's angle, and the
inradius, circumradius and height of the simplex; the distances to the midpoint and to the foot
of the bisector), and for the regular polygon with the vertices `ρ(cos(2πk/n), sin(2πk/n))`;
the diagonals are the pairs of vertices that are not the ends of a side. Their formulas (Heron,
the law of cosines, `Δ/s`, `abc/(4Δ)`, `(n-2)π/n`, `n(n-3)/2`, …) are theorems, not
definitions. -/

namespace Leanify.Triangles
open Build Core

def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def tan (x : B) : B := app (prim (.realFn .tan)) x
def pi : B := prim .pi
def pos (x : B) : B := lt (num 0) x
def tri (a b c : B) : B := and (and (pos a) (pos b)) (and (pos c) (and (lt a (add b c)) (and (lt b (add a c)) (lt c (add a b)))))
def semi (a b c : B) : B := div (add (add a b) c) (num 2)
def side (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [none, none, dom3 .real tri], doc, value := .const c }
def ngon (n : B) : B := and (isInt n) (le (num 3) n)
def poly (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real ngon, dom1 .real pos], doc, value := .const c }

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def area : Nat := 0
def angleOpposite : Nat := 1
def inradius : Nat := 2
def circumradius : Nat := 3
def altitude : Nat := 4
def median : Nat := 5
def bisector : Nat := 6
def interiorAngle : Nat := 7
def polygonArea : Nat := 8
def polygonCircumradius : Nat := 9
def apothem : Nat := 10
def diagonals : Nat := 11
end Const

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\operatorname{area}_{#1,#2,#3}", w!"\\gamma_{#1}(#2,#3)", w!"r_{#1,#2,#3}", w!"R_{#1,#2,#3}",
    w!"h_{#1}(#2,#3)", w!"m_{#1}(#2,#3)", w!"w_{#1}(#2,#3)", w!"\\theta_{#1,#2}", w!"\\operatorname{area}_{#1,#2}",
    w!"R_{#1,#2}", w!"\\operatorname{apo}_{#1,#2}", w!"\\operatorname{diag}"]
  constLean := [w!"Leanify.Triangles.area", w!"Leanify.Triangles.angleOpposite", w!"Leanify.Triangles.inradius",
    w!"Leanify.Triangles.circumradius", w!"Leanify.Triangles.altitude", w!"Leanify.Triangles.median",
    w!"Leanify.Triangles.bisector", w!"Leanify.Triangles.interiorAngle", w!"Leanify.Triangles.polygonArea",
    w!"Leanify.Triangles.polygonCircumradius", w!"Leanify.Triangles.apothem", w!"Leanify.Triangles.diagonals"]
  modules := [w!"Leanify.Library.TrianglesModel"]
  notions := [
    { name := phrase!"semiperimeter of the triangle with sides $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real tri], doc := "`s = (a + b + c)/2`",
      value := close <| lamR fun a => lamR fun b => lamT .real (fun c => tri a b c) fun c => semi a b c },
    side phrase!"area of the triangle with sides $v$, $v$ and $v$" Const.area
      "the Lebesgue measure of a triangle of the plane with these sides (`√(s(s-a)(s-b)(s-c))`, Heron)",
    side phrase!"angle opposite $v$ in the triangle with sides $v$ and $v$" Const.angleOpposite
      "the angle where the sides `a` and `b` meet (Mathlib `EuclideanGeometry.angle`; `cos γ = (a² + b² - c²)/(2ab)`)",
    side phrase!"inradius of the triangle with sides $v$, $v$ and $v$" Const.inradius
      "Mathlib `Affine.Simplex.inradius` (`Δ/s`)",
    side phrase!"circumradius of the triangle with sides $v$, $v$ and $v$" Const.circumradius
      "Mathlib `Affine.Simplex.circumradius` (`abc/(4Δ)`)",
    side phrase!"altitude to $v$ in the triangle with sides $v$ and $v$" Const.altitude
      "the height of the vertex opposite `c` (Mathlib `Affine.Simplex.height`; `2Δ/c`)",
    side phrase!"median to $v$ in the triangle with sides $v$ and $v$" Const.median
      "the distance from the vertex opposite `c` to the midpoint of `c` (`½ √(2a² + 2b² - c²)`)",
    side phrase!"bisector of the angle opposite $v$ in the triangle with sides $v$ and $v$" Const.bisector
      "the distance from the vertex opposite `c` to the point of `c` on the bisector (`√(ab((a+b)² - c²))/(a+b)`)",
    poly phrase!"interior angle of the regular polygon with $v$ sides of length $v$" Const.interiorAngle
      "the angle at a vertex between its neighbours (`(n-2)π/n`)",
    poly phrase!"area of the regular polygon with $v$ sides of length $v$" Const.polygonArea
      "the Lebesgue measure of the convex hull of its vertices (`n s²/(4 tan(π/n))`)",
    poly phrase!"circumradius of the regular polygon with $v$ sides of length $v$" Const.polygonCircumradius
      "the radius of the circle through its vertices (`s/(2 sin(π/n))`)",
    poly phrase!"apothem of the regular polygon with $v$ sides of length $v$" Const.apothem
      "the distance from its centre to a side, the inradius (`s/(2 tan(π/n))`)",
    { name := phrase!"number of diagonals of a convex polygon with $v$ vertices", ty := .real ⟶ .real, doms := [dom1 .real ngon],
      doc := "the pairs of vertices that are not the ends of a side (`n(n-3)/2`)", value := .const Const.diagonals }]

end Leanify.Triangles
