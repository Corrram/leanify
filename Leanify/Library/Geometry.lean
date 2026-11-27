import Leanify.Library.Core

/-! # Vocabulary: the Euclidean plane

A point is a point of the plane (a pair of real numbers): a type of its own, so that an
article binds points as it binds numbers (`Let $A$, $B$ and $C$ be points.`) and speaks of
figures as sets of points (`a point $P$ lying on $C$`).

* nouns: `point`, `point of the plane`;
* adjectives: `lying on $C$` (a set of points), `collinear with $A$ and $B$`, `equidistant from
  $A$ and $B$`, `distinct from $A$`;
* notions: the point `$(x,y)$`, the origin, the coordinates of a point, the distance
  between two points, the midpoint, the area, perimeter and centroid of a triangle, the
  angle at a point, the slope of a line; and the figures: the line through two points, the
  segment, the perpendicular bisector, the circle and the disc with a centre and a radius.

In formulas, `|AB|` is the distance and `\angle ABC` the angle at `B` between `A` and `C`.
The line through `A` and `B` asks that they are distinct, the angle at `B` between `A` and
`C` that both differ from `B`, a circle that its radius is positive. The constants are
interpreted by `Leanify/Library/GeometryModel.lean`. -/

namespace Leanify.Geometry
open Build Core

/-- Points of the plane: the field's base type. -/
abbrev P : Ty := .base 0
/-- Figures: sets of points. -/
abbrev Fig : Ty := P ⟶ .prop

/-- The constants, in the order of their indices: `(type, TeX name, Lean name)`. -/
def table : List (Ty × Codes × Codes) := [
  (.real ⟶ .real ⟶ P, w!"(#1,#2)", w!"Leanify.Geometry.point"),                         -- 0
  (P ⟶ .real, w!"x", w!"Leanify.Geometry.xCoord"),                                       -- 1
  (P ⟶ .real, w!"y", w!"Leanify.Geometry.yCoord"),                                       -- 2
  (P ⟶ P ⟶ .real, w!"\\lvert #1#2\\rvert", w!"Leanify.Geometry.dist"),                   -- 3
  (P ⟶ P ⟶ P, w!"\\operatorname{mid}", w!"Leanify.Geometry.midpoint"),                  -- 4
  (P ⟶ P ⟶ P ⟶ .real, w!"\\operatorname{area}", w!"Leanify.Geometry.area"),             -- 5
  (P ⟶ P ⟶ P ⟶ .real, w!"\\angle #2#1#3", w!"Leanify.Geometry.angle"),                   -- 6
  (P ⟶ P ⟶ P ⟶ .prop, w!"\\operatorname{Collinear}", w!"Leanify.Geometry.Collinear"),   -- 7
  (P ⟶ P ⟶ P ⟶ P, w!"\\operatorname{centroid}", w!"Leanify.Geometry.centroid")]         -- 8

def lamP (body : B → B) : B := lamT P (fun _ => tt) body
def d (a b : B) : B := app2 (const 3) a b
def c3 (i : Nat) (a b c : B) : B := app (app (app (const i) a) b) c
def xc (a : B) : B := app (const 1) a
def distinct (a b : B) : B := not (eq a b)

def mod (p : Phrase) (pred : Tm) (doc : String) : Modifier := { phrase := p, prenominal := false, ty := P, pred, doc }
def n2 (name : Phrase) (ty : Ty) (body : B → B → B) (doc : String) : Notion :=
  { name, ty, doc, value := close <| lamP fun a => lamP fun b => body a b }
def n3 (name : Phrase) (ty : Ty) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty, doc, value := close <| lamP fun a => lamP fun b => lamP fun c => body a b c }
/-- A figure with a centre and a positive radius. -/
def round (name : Phrase) (rel : B → B → B) (doc : String) : Notion :=
  { name, ty := P ⟶ .real ⟶ Fig, doc, value := close <| lamP fun c => lamR fun r =>
      guard (lt (num 0) r) (lamP fun p => rel (d p c) r) }

def vocab : Vocab where
  types := [w!"\\mathrm{Point}"]
  consts := table.map (·.1)
  constNames := table.map (·.2.1)
  constLean := table.map (·.2.2)
  typeLean := [(w!"Leanify.Geometry.Point", w!"Leanify.Geometry.Point.origin")]
  modules := [w!"Leanify.Library.GeometryModel"]
  methods := [
    ⟨P, .fn w!"@dist", 3, "`|AB|`, the distance between two points", none⟩,
    ⟨P, .fn w!"\\angle", 6, "`\\angle ABC`, the angle at `B` between `A` and `C` (in `[0, π]`), for `A ≠ B` and `C ≠ B`",
      some (close <| lamP fun b => lamP fun a => lamP fun c => and (distinct a b) (distinct c b))⟩]
  nouns := [
    { sing := phrase!"point", plural := phrase!"points", ty := P, pred := close (lamP fun _ => tt),
      doc := "a point of the Euclidean plane (`ℝ × ℝ`)" },
    { sing := phrase!"point of the plane", plural := phrase!"points of the plane", ty := P, pred := close (lamP fun _ => tt),
      doc := "`ℝ × ℝ`" }]
  mods := [
    mod phrase!"lying on $v$" (close <| lamT Fig (fun _ => tt) fun f => lamP fun p => app f p) "a point of the figure",
    mod phrase!"collinear with $v$ and $v$" (close <| lamP fun a => lamP fun b => lamP fun p => c3 7 a b p)
      "on a line with them",
    mod phrase!"equidistant from $v$ and $v$" (close <| lamP fun a => lamP fun b => lamP fun p => eq (d p a) (d p b))
      "`|PA| = |PB|`",
    mod phrase!"distinct from $v$" (close <| lamP fun a => lamP fun p => distinct p a) "`P ≠ A`"]
  notions := [
    { name := phrase!"point $(v,v)$", value := .const 0, ty := .real ⟶ .real ⟶ P, doc := "with these coordinates" },
    { name := phrase!"origin", value := close (app2 (const 0) (num 0) (num 0)), ty := P, doc := "`(0,0)`" },
    { name := phrase!"$x$-coordinate of $v$", value := .const 1, ty := P ⟶ .real, doc := "the first coordinate" },
    { name := phrase!"$y$-coordinate of $v$", value := .const 2, ty := P ⟶ .real, doc := "the second coordinate" },
    { name := phrase!"abscissa of $v$", value := .const 1, ty := P ⟶ .real, doc := "the first coordinate" },
    { name := phrase!"ordinate of $v$", value := .const 2, ty := P ⟶ .real, doc := "the second coordinate" },
    { name := phrase!"distance between $v$ and $v$", value := .const 3, ty := P ⟶ P ⟶ .real, doc := "the Euclidean distance" },
    { name := phrase!"distance from $v$ to $v$", value := .const 3, ty := P ⟶ P ⟶ .real, doc := "the Euclidean distance" },
    { name := phrase!"midpoint of $v$ and $v$", value := .const 4, ty := P ⟶ P ⟶ P, doc := "`(A + B)/2`" },
    { name := phrase!"area of the triangle with vertices $v$, $v$ and $v$", value := .const 5, ty := P ⟶ P ⟶ P ⟶ .real,
      doc := "`0` for collinear points" },
    n3 phrase!"perimeter of the triangle with vertices $v$, $v$ and $v$" (P ⟶ P ⟶ P ⟶ .real)
      (fun a b c => add (add (d a b) (d b c)) (d c a)) "`|AB| + |BC| + |CA|`",
    { name := phrase!"centroid of the triangle with vertices $v$, $v$ and $v$", value := .const 8, ty := P ⟶ P ⟶ P ⟶ P,
      doc := "`(A + B + C)/3`" },
    n3 phrase!"angle at $v$ between $v$ and $v$" (P ⟶ P ⟶ P ⟶ .real)
      (fun b a c => guard (and (distinct a b) (distinct c b)) (c3 6 b a c))
      "`∠ABC` in `[0, π]`, for `A ≠ B` and `C ≠ B`",
    n2 phrase!"slope of the line through $v$ and $v$" (P ⟶ P ⟶ .real)
      (fun a b => guard (not (eq (xc a) (xc b))) (div (sub (app (const 2) b) (app (const 2) a)) (sub (xc b) (xc a))))
      "for points with different first coordinates",
    n2 phrase!"line through $v$ and $v$" (P ⟶ P ⟶ Fig)
      (fun a b => guard (distinct a b) (lamP fun p => c3 7 a b p)) "of two distinct points",
    n2 phrase!"segment from $v$ to $v$" (P ⟶ P ⟶ Fig)
      (fun a b => lamP fun p => eq (add (d a p) (d p b)) (d a b)) "the points between them: `|AP| + |PB| = |AB|`",
    n2 phrase!"perpendicular bisector of $v$ and $v$" (P ⟶ P ⟶ Fig)
      (fun a b => guard (distinct a b) (lamP fun p => eq (d p a) (d p b))) "the points equidistant from two distinct points",
    round phrase!"circle with centre $v$ and radius $v$" (fun x r => eq x r) "`{P : |PC| = r}`, `r > 0`",
    round phrase!"circle with center $v$ and radius $v$" (fun x r => eq x r) "`{P : |PC| = r}`, `r > 0`",
    round phrase!"disc with centre $v$ and radius $v$" (fun x r => le x r) "`{P : |PC| ≤ r}`, `r > 0`",
    round phrase!"disk with center $v$ and radius $v$" (fun x r => le x r) "`{P : |PC| ≤ r}`, `r > 0`"]

end Leanify.Geometry
