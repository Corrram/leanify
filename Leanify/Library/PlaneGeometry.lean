import Leanify.Library.Geometry

/-! # Vocabulary: lines, triangle centres and conics in the plane

More of the Euclidean plane of the field `geometry`, which this field includes: the
distance from a point to a line, the foot of a perpendicular and a reflection, the centres
and radii of a triangle, and the conics by their foci (`Let $E$ be the ellipse with foci $A$
and $B$ and semi-major axis $2$.`, `$P$ is a point lying on $E$`).

* notions of points and lines: the distance from `P` to the line through `A` and `B`, the
  foot of the perpendicular from `P` to that line, the reflection of `P` in it;
* notions of a triangle with vertices `A`, `B`, `C` (not collinear): the circumcentre and
  circumradius, the incentre and inradius, the orthocentre (also `-center`);
* conics, as figures: the ellipse with foci `F₁`, `F₂` and semi-major axis `a`
  (`|PF₁| + |PF₂| = 2a`, `2a > |F₁F₂|`), the hyperbola (`||PF₁| - |PF₂|| = 2a`,
  `0 < 2a < |F₁F₂|`), the parabola with focus `F` and directrix the line through `A` and `B`
  (`F` not on it), and the eccentricity of an ellipse.

Every meaning is a term of the core language with the constants of `geometry` (the point
with given coordinates, the coordinates, distances, areas, collinearity); a centre that is
described by its property is defined for a triangle that is not degenerate. -/

namespace Leanify.PlaneGeometry
open Build Core
open Leanify.Geometry (P Fig lamP d c3 xc)

def yc (a : B) : B := app (const 2) a
def pt (x y : B) : B := app2 (const 0) x y
def area (a b c : B) : B := c3 5 a b c
def collinear (a b c : B) : B := c3 7 a b c
/-- `(P - A)·(B - C)`. -/
def dot (p a b c : B) : B := add (mul (sub (xc p) (xc a)) (sub (xc b) (xc c))) (mul (sub (yc p) (yc a)) (sub (yc b) (yc c)))
/-- `t` with `A + t(B - A)` the foot of the perpendicular from `P`. -/
def footT (p a b : B) : B := div (dot p a b a) (mul (d a b) (d a b))
def foot (p a b : B) : B :=
  pt (add (xc a) (mul (footT p a b) (sub (xc b) (xc a)))) (add (yc a) (mul (footT p a b) (sub (yc b) (yc a))))
def lineDist (p a b : B) : B := div (mul (num 2) (area a b p)) (d a b)
def nondeg (a b c : B) : B := not (collinear a b c)
def theP (body : B → B) : B := theT P body
def circumcentre (a b c : B) : B := theP fun o => and (eq (d o a) (d o b)) (eq (d o b) (d o c))
def orthocentre (a b c : B) : B := theP fun h => and (eq (dot h a b c) (num 0)) (eq (dot h b c a) (num 0))
def incentre (a b c : B) : B :=
  let la := d b c
  let lb := d c a
  let lc := d a b
  let s := add (add la lb) lc
  pt (div (add (add (mul la (xc a)) (mul lb (xc b))) (mul lc (xc c))) s)
    (div (add (add (mul la (yc a)) (mul lb (yc b))) (mul lc (yc c))) s)
def perimeter (a b c : B) : B := add (add (d a b) (d b c)) (d c a)

/-- A point or a number of a triangle that is not degenerate. -/
def tri (name : Phrase) (ty : Ty) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := P ⟶ P ⟶ P ⟶ ty, doms := [none, none, dom3 P nondeg], doc,
    value := close <| lamP fun a => lamP fun b => lamT P (fun c => nondeg a b c) fun c => body a b c }
/-- Of a point and the line through `A ≠ B`. -/
def ofLine (name : Phrase) (ty : Ty) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := P ⟶ P ⟶ P ⟶ ty, doms := [none, none, dom2 P fun a b => ne a b], doc,
    value := close <| lamP fun p => lamP fun a => lamT P (fun b => ne a b) fun b => body p a b }
def ellDom (f g a : B) : B := lt (d f g) (mul (num 2) a)
def hypDom (f g a : B) : B := and (lt (num 0) a) (lt (mul (num 2) a) (d f g))
def conic (name : Phrase) (dm : B → B → B → B) (rel : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := P ⟶ P ⟶ .real ⟶ Fig, doms := [none, none, dom3 .real dm], doc,
    value := close <| lamP fun f => lamP fun g => lamT .real (fun a => dm f g a) fun a => lamP fun p => rel f g a p }

/-- The words of the field itself. -/
def own : Vocab where
  notions := [
    ofLine phrase!"distance from $v$ to the line through $v$ and $v$" .real lineDist
      "`2 area(A,B,P)/|AB|`, `A ≠ B`",
    ofLine phrase!"foot of the perpendicular from $v$ to the line through $v$ and $v$" P foot
      "the point of the line nearest to `P`, `A ≠ B`",
    ofLine phrase!"reflection of $v$ in the line through $v$ and $v$" P
      (fun p a b => pt (sub (mul (num 2) (xc (foot p a b))) (xc p)) (sub (mul (num 2) (yc (foot p a b))) (yc p)))
      "`2F - P` with `F` the foot of the perpendicular, `A ≠ B`",
    tri phrase!"circumcentre of the triangle with vertices $v$, $v$ and $v$" P circumcentre
      "the point equidistant from the vertices, of a triangle that is not degenerate",
    tri phrase!"circumcenter of the triangle with vertices $v$, $v$ and $v$" P circumcentre "the circumcentre",
    tri phrase!"circumradius of the triangle with vertices $v$, $v$ and $v$" .real (fun a b c => d (circumcentre a b c) a)
      "the distance from the circumcentre to a vertex",
    tri phrase!"incentre of the triangle with vertices $v$, $v$ and $v$" P incentre
      "`(aA + bB + cC)/(a + b + c)` with the side lengths opposite the vertices",
    tri phrase!"incenter of the triangle with vertices $v$, $v$ and $v$" P incentre "the incentre",
    tri phrase!"inradius of the triangle with vertices $v$, $v$ and $v$" .real
      (fun a b c => div (mul (num 2) (area a b c)) (perimeter a b c)) "`2 area/perimeter`",
    tri phrase!"orthocentre of the triangle with vertices $v$, $v$ and $v$" P orthocentre
      "the common point of the altitudes",
    tri phrase!"orthocenter of the triangle with vertices $v$, $v$ and $v$" P orthocentre "the orthocentre",
    conic phrase!"ellipse with foci $v$ and $v$ and semi-major axis $v$" ellDom
      (fun f g a p => eq (add (d p f) (d p g)) (mul (num 2) a)) "`{P : |PF₁| + |PF₂| = 2a}`, `2a > |F₁F₂|`",
    conic phrase!"hyperbola with foci $v$ and $v$ and semi-major axis $v$" hypDom
      (fun f g a p => eq (abs (sub (d p f) (d p g))) (mul (num 2) a)) "`{P : ||PF₁| - |PF₂|| = 2a}`, `0 < 2a < |F₁F₂|`",
    { name := phrase!"parabola with focus $v$ and directrix through $v$ and $v$", ty := P ⟶ P ⟶ P ⟶ Fig,
      doms := [none, none, dom3 P nondeg], doc := "`{P : |PF| = dist(P, AB)}`, `F` not on the line `AB`",
      value := close <| lamP fun f => lamP fun a => lamT P (fun b => nondeg f a b) fun b => lamP fun p => eq (d p f) (lineDist p a b) },
    { name := phrase!"eccentricity of the ellipse with foci $v$ and $v$ and semi-major axis $v$", ty := P ⟶ P ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real ellDom], doc := "`|F₁F₂|/(2a)`",
      value := close <| lamP fun f => lamP fun g => lamT .real (fun a => ellDom f g a) fun a => div (d f g) (mul (num 2) a) }]

/-- `geometry` with these words: one vocabulary, so that the words of this field use the type
and the constants of `geometry` as they are numbered there. -/
def vocab : Vocab :=
  let G := Vocab.tag w!"geometry" Geometry.vocab
  let O := Vocab.tag w!"planegeometry" own
  { G with notions := G.notions ++ O.notions }

end Leanify.PlaneGeometry
