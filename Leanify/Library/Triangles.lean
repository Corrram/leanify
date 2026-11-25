import Leanify.Library.Core

/-! # Vocabulary: triangles by their sides, and regular polygons

The metric quantities of a triangle with side lengths `a`, `b`, `c` (`We write $\Delta(a,b,c)$
for the area of the triangle with sides $a$, $b$ and $c$.`) and of a regular `n`-gon with side
`s`; the triangles by their points are in the field `planegeometry`.

* notions, for positive `a, b, c` with `a < b + c`, `b < a + c`, `c < a + b`: the semiperimeter,
  the area (Heron's formula), the angle opposite `c` (the `γ ∈ (0,π)` with `cos γ =
  (a² + b² - c²)/(2ab)`), the inradius `Δ/s`, the circumradius `abc/(4Δ)`, the altitude to `c`
  (`2Δ/c`), the median to `c` (`½ √(2a² + 2b² - c²)`), the bisector of the angle opposite `c`
  (`√(ab((a+b)² - c²))/(a+b)`); for a regular `n`-gon (`n ≥ 3`) with side `s`: the interior angle
  `(n-2)π/n`, the area `n s²/(4 tan(π/n))`, the circumradius `s/(2 sin(π/n))`, the apothem
  `s/(2 tan(π/n))`, and the number of diagonals of a convex `n`-gon `n(n-3)/2`. A right or an
  acute triangle is said by its angles (`the angle opposite $c$ … is $\frac{\pi}{2}$`).

Every meaning is a term of the core language. -/

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
def heron (a b c : B) : B :=
  sqrt (mul (mul (semi a b c) (sub (semi a b c) a)) (mul (sub (semi a b c) b) (sub (semi a b c) c)))
def sq (x : B) : B := mul x x
def side (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [none, none, dom3 .real tri], doc,
    value := close <| lamR fun a => lamR fun b => lamT .real (fun c => tri a b c) fun c => body a b c }
def ngon (n : B) : B := and (isInt n) (le (num 3) n)
def poly (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real ngon, dom1 .real pos], doc,
    value := close <| lamT .real ngon fun n => lamT .real pos fun s => body n s }

def vocab : Vocab where
  notions := [
    side phrase!"semiperimeter of the triangle with sides $v$, $v$ and $v$" semi "`s = (a + b + c)/2`",
    side phrase!"area of the triangle with sides $v$, $v$ and $v$" heron "`√(s(s-a)(s-b)(s-c))` (Heron)",
    side phrase!"angle opposite $v$ in the triangle with sides $v$ and $v$"
      (fun c a b => theR fun g => and (and (lt (num 0) g) (lt g pi)) (eq (cos g) (div (sub (add (sq a) (sq b)) (sq c)) (mul (num 2) (mul a b)))))
      "the `γ ∈ (0,π)` with `cos γ = (a² + b² - c²)/(2ab)` (law of cosines)",
    side phrase!"inradius of the triangle with sides $v$, $v$ and $v$" (fun a b c => div (heron a b c) (semi a b c)) "`Δ/s`",
    side phrase!"circumradius of the triangle with sides $v$, $v$ and $v$" (fun a b c => div (mul (mul a b) c) (mul (num 4) (heron a b c)))
      "`abc/(4Δ)`",
    side phrase!"altitude to $v$ in the triangle with sides $v$ and $v$" (fun c a b => div (mul (num 2) (heron a b c)) c) "`2Δ/c`",
    side phrase!"median to $v$ in the triangle with sides $v$ and $v$"
      (fun c a b => div (sqrt (sub (add (mul (num 2) (sq a)) (mul (num 2) (sq b))) (sq c))) (num 2)) "`½ √(2a² + 2b² - c²)`",
    side phrase!"bisector of the angle opposite $v$ in the triangle with sides $v$ and $v$"
      (fun c a b => div (sqrt (mul (mul a b) (sub (sq (add a b)) (sq c)))) (add a b)) "`√(ab((a+b)² - c²))/(a+b)`",
    poly phrase!"interior angle of the regular polygon with $v$ sides of length $v$" (fun n _ => div (mul (sub n (num 2)) pi) n)
      "`(n-2)π/n`",
    poly phrase!"area of the regular polygon with $v$ sides of length $v$" (fun n s => div (mul n (sq s)) (mul (num 4) (tan (div pi n))))
      "`n s²/(4 tan(π/n))`",
    poly phrase!"circumradius of the regular polygon with $v$ sides of length $v$" (fun n s => div s (mul (num 2) (sin (div pi n))))
      "`s/(2 sin(π/n))`",
    poly phrase!"apothem of the regular polygon with $v$ sides of length $v$" (fun n s => div s (mul (num 2) (tan (div pi n))))
      "`s/(2 tan(π/n))`, the inradius",
    { name := phrase!"number of diagonals of a convex polygon with $v$ vertices", ty := .real ⟶ .real, doms := [dom1 .real ngon],
      doc := "`n(n-3)/2`", value := close <| lamT .real ngon fun n => div (mul n (sub n (num 3))) (num 2) }]

end Leanify.Triangles
