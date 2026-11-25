import Leanify.Library.Core

/-! # Vocabulary: map projections

The coordinates and scale factors of the classical projections of the unit sphere, by latitude
`φ` and longitude `λ` in radians (`We write $y(\phi)$ for the Mercator ordinate of the latitude
$\phi$.`). Distances on the sphere are in the field `sphericalgeometry`.

* notions: the Mercator ordinate `log tan(π/4 + φ/2)` and scale factor `sec φ`; the ordinate
  `sin φ` of the Lambert cylindrical equal-area projection; the coordinates
  `2 cos φ sin λ/(1 + cos φ cos λ)` and `2 sin φ/(1 + cos φ cos λ)` of the stereographic
  projection from the antipode of `(0,0)`; the coordinates `λ cos φ` (sinusoidal) of an
  equal-area pseudocylindrical projection; the inverse Mercator latitude `2 arctan(e^y) - π/2`.

Every meaning is a term of the core language. -/

namespace Leanify.MapProjections
open Build Core

def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def tan (x : B) : B := app (prim (.realFn .tan)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def pi : B := prim .pi
def openLat (p : B) : B := and (lt (neg (div pi (num 2))) p) (lt p (div pi (num 2)))
def lat (p : B) : B := and (le (neg (div pi (num 2))) p) (le p (div pi (num 2)))
def stereo (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real lat, dom2 .real fun p l => lt (num 0) (add (num 1) (mul (cos p) (cos l)))], doc,
    value := close <| lamT .real lat fun p => lamT .real (fun l => lt (num 0) (add (num 1) (mul (cos p) (cos l)))) fun l => body p l }

def vocab : Vocab where
  notions := [
    { name := phrase!"Mercator ordinate of the latitude $v$", ty := .real ⟶ .real, doms := [dom1 .real openLat],
      doc := "`log tan(π/4 + φ/2)`", value := close <| lamT .real openLat fun p => log (tan (add (div pi (num 4)) (div p (num 2)))) },
    { name := phrase!"Mercator scale factor at the latitude $v$", ty := .real ⟶ .real, doms := [dom1 .real openLat],
      doc := "`sec φ`", value := close <| lamT .real openLat fun p => div (num 1) (cos p) },
    { name := phrase!"latitude of the Mercator ordinate $v$", ty := .real ⟶ .real,
      doc := "`2 arctan(e^y) - π/2` (the Gudermannian function): the `φ ∈ (-π/2, π/2)` whose Mercator ordinate is `y`",
      value := close <| lamR fun y => theR fun p => and (openLat p) (eq (tan (add (div pi (num 4)) (div p (num 2)))) (exp y)) },
    { name := phrase!"Lambert equal-area ordinate of the latitude $v$", ty := .real ⟶ .real, doms := [dom1 .real lat],
      doc := "`sin φ`", value := close <| lamT .real lat fun p => sin p },
    { name := phrase!"sinusoidal abscissa of the point with latitude $v$ and longitude $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real lat, none], doc := "`λ cos φ`",
      value := close <| lamT .real lat fun p => lamR fun l => mul l (cos p) },
    stereo phrase!"stereographic abscissa of the point with latitude $v$ and longitude $v$"
      (fun p l => div (mul (num 2) (mul (cos p) (sin l))) (add (num 1) (mul (cos p) (cos l)))) "`2 cos φ sin λ/(1 + cos φ cos λ)`",
    stereo phrase!"stereographic ordinate of the point with latitude $v$ and longitude $v$"
      (fun p l => div (mul (num 2) (sin p)) (add (num 1) (mul (cos p) (cos l)))) "`2 sin φ/(1 + cos φ cos λ)`"]

end Leanify.MapProjections
