import Leanify.Library.Core

/-! # Vocabulary: polyhedra

Euler's formula and the combinatorics and angles of the Platonic solids by their faces
(`We write $V(p,q)$ for the number of vertices of the Platonic solid with faces of $p$ sides and
$q$ faces at each vertex.`). Volumes are in the field `solids`.

* notions: the Euler characteristic `V - E + F` of a polyhedron; the numbers of vertices
  `4p/D`, edges `2pq/D` and faces `4q/D` of the Platonic solid `{p,q}` (faces with `p` sides,
  `q` at each vertex), `D = 4 - (p-2)(q-2) > 0`; its dihedral angle (`sin(θ/2) = cos(π/q)/sin(π/p)`);
  the angle defect `2π - s` of a vertex with face angles summing to `s` (Descartes: the defects
  of a convex polyhedron add up to `4π`).

Every meaning is a term of the core language. -/

namespace Leanify.Polyhedra
open Build Core

def ge3 (n : B) : B := and (isInt n) (le (num 3) n)
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def dd (p q : B) : B := sub (num 4) (mul (sub p (num 2)) (sub q (num 2)))
def platonic (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real ge3, dom2 .real fun p q => and (ge3 q) (lt (num 0) (dd p q))], doc,
    value := close <| lamT .real ge3 fun p => lamT .real (fun q => and (ge3 q) (lt (num 0) (dd p q))) fun q => body p q }

def vocab : Vocab where
  notions := [
    { name := phrase!"Euler characteristic of a polyhedron with $v$ vertices, $v$ edges and $v$ faces", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`V - E + F`, which is `2` for a convex polyhedron",
      value := close <| lamR fun v => lamR fun e => lamR fun f => add (sub v e) f },
    platonic phrase!"number of vertices of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      (fun p q => div (mul (num 4) p) (dd p q)) "`4p/(4 - (p-2)(q-2))`",
    platonic phrase!"number of edges of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      (fun p q => div (mul (num 2) (mul p q)) (dd p q)) "`2pq/(4 - (p-2)(q-2))`",
    platonic phrase!"number of faces of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      (fun p q => div (mul (num 4) q) (dd p q)) "`4q/(4 - (p-2)(q-2))`",
    platonic phrase!"dihedral angle of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      (fun p q => theR fun t => and (and (lt (num 0) t) (lt t pi)) (eq (sin (div t (num 2))) (div (cos (div pi q)) (sin (div pi p)))))
      "the `θ ∈ (0, π)` with `sin(θ/2) = cos(π/q)/sin(π/p)`",
    { name := phrase!"angle defect of a vertex with face angles summing to $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun s => and (lt (num 0) s) (lt s (mul (num 2) pi))],
      doc := "`2π - s`", value := close <| lamT .real (fun s => and (lt (num 0) s) (lt s (mul (num 2) pi))) fun s => sub (mul (num 2) pi) s }]

end Leanify.Polyhedra
